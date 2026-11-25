module

public import Section2.ResidueOrder

/-! Transport of leading terms along embeddings of valued fields. This is
the algebraic part of Propositions 2.13 and Lemma 2.20. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K F : Type*} [Field K] [Field F] (O : ValuationSubring K) (P : ValuationSubring F)

/-- The predicate for an embedding of valuation-ring pairs. -/
abbrev RespectsValuationRing (f : K →+* F) : Prop :=
  ∀ x, f x ∈ P ↔ x ∈ O

theorem rv_map_eq_iff {f : K →+* F} (hf : RespectsValuationRing O P f)
    (x y : K) : rv P (f x) = rv P (f y) ↔ rv O x = rv O y := by
  by_cases hy : y = 0
  · simp only [hy, map_zero, rv_eq_zero_iff, map_eq_zero]
  rw [rv_eq_rv_iff_ring P (map_ne_zero f |>.mpr hy), rv_eq_rv_iff_ring O hy,
    ← map_sub, ← map_div₀, ← map_inv₀, hf, f.injective.eq_iff]

private def representative (t : RV0 O) : K := Classical.choose (rv_surjective O t)

private theorem rv_representative (t : RV0 O) : rv O (representative O t) = t :=
  Classical.choose_spec (rv_surjective O t)

/-- The unique map of leading terms induced by an embedding of the
valued-field reducts. -/
def mapRV (f : K →+* F) (hf : RespectsValuationRing O P f) : RV0 O ↪ RV0 P where
  toFun t := rv P (f (representative O t))
  inj' := by
    intro s t h
    change rv P (f (representative O s)) = rv P (f (representative O t)) at h
    exact (rv_representative O s).symm.trans
      (((rv_map_eq_iff O P hf _ _).mp h).trans (rv_representative O t))

@[simp] theorem mapRV_rv (f : K →+* F) (hf : RespectsValuationRing O P f) (x : K) :
    mapRV O P f hf (rv O x) = rv P (f x) :=
  (rv_map_eq_iff O P hf _ _).mpr (rv_representative O (rv O x))

theorem mapRV_unique (f : K →+* F) (hf : RespectsValuationRing O P f)
    {g : RV0 O → RV0 P} (h : ∀ x, g (rv O x) = rv P (f x)) :
    g = mapRV O P f hf := by
  funext t
  obtain ⟨x, rfl⟩ := rv_surjective O t
  rw [h, mapRV_rv]

theorem mapRV_mul (f : K →+* F) (hf : RespectsValuationRing O P f) (s t : RV0 O) :
    mapRV O P f hf (s * t) = mapRV O P f hf s * mapRV O P f hf t := by
  obtain ⟨x, rfl⟩ := rv_surjective O s
  obtain ⟨y, rfl⟩ := rv_surjective O t
  rw [← map_mul (rv O), mapRV_rv, map_mul f, map_mul (rv P), mapRV_rv, mapRV_rv]

theorem mapRV_inv (f : K →+* F) (hf : RespectsValuationRing O P f) (t : RV0 O) :
    mapRV O P f hf t⁻¹ = (mapRV O P f hf t)⁻¹ := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  calc
    mapRV O P f hf ((rv O x)⁻¹) = mapRV O P f hf (rv O x⁻¹) :=
      congrArg (mapRV O P f hf) (rv_inv O x).symm
    _ = rv P (f x⁻¹) := mapRV_rv O P f hf x⁻¹
    _ = (mapRV O P f hf (rv O x))⁻¹ := by
      rw [map_inv₀ f x, rv_inv P (f x), mapRV_rv]

theorem mapRV_zero (f : K →+* F) (hf : RespectsValuationRing O P f) :
    mapRV O P f hf 0 = 0 := by
  rw [← map_zero (rv O), mapRV_rv, map_zero, map_zero]

theorem mapRV_one (f : K →+* F) (hf : RespectsValuationRing O P f) :
    mapRV O P f hf 1 = 1 := by
  rw [← map_one (rv O), mapRV_rv, map_one, map_one]

private theorem valuation_eq_one_iff (x : K) :
    O.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ O ∧ x⁻¹ ∈ O := by
  by_cases hx : x = 0
  · simp [hx]
  rw [O.valuation_le_one_iff x |>.symm, O.valuation_le_one_iff x⁻¹ |>.symm, map_inv₀]
  have hv : O.valuation x ≠ 0 := (map_ne_zero O.valuation).mpr hx
  rw [inv_le_one₀ (pos_iff_ne_zero.mpr hv), and_iff_right hx, le_antisymm_iff]

theorem mapRV_value_one_iff (f : K →+* F) (hf : RespectsValuationRing O P f) (t : RV0 O) :
    unsignedValue P (mapRV O P f hf t) = 1 ↔ unsignedValue O t = 1 := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  rw [mapRV_rv, unsignedValue_rv, unsignedValue_rv, valuation_eq_one_iff,
    valuation_eq_one_iff, ← map_inv₀ f, hf, hf, map_ne_zero]

variable [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder F] [IsStrictOrderedRing F]

theorem mapRV_strictMono (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (f : K →+* F) (hf : RespectsValuationRing O P f) (hmono : StrictMono f) :
    letI := rvLinearOrder O hO
    letI := rvLinearOrder P hP
    StrictMono (mapRV O P f hf) := by
  intro s t h
  obtain ⟨x, rfl⟩ := rv_surjective O s
  obtain ⟨y, rfl⟩ := rv_surjective O t
  rw [mapRV_rv, mapRV_rv]
  obtain ⟨hxy, hne⟩ := (rv_lt_rv_iff O hO).mp h
  exact (rv_lt_rv_iff P hP).mpr ⟨hmono hxy, hne ∘ (rv_map_eq_iff O P hf _ _).mp⟩

end GeneralizedEuler.Section2
