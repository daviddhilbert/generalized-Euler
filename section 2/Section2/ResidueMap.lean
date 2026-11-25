module

public import Section2.LeadingTermMap
public import Section2.SortedStructure
public import Section2.ResidueOrder

/-! Compatibility of residue maps and leading-term maps. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K F : Type*} [Field K] [Field F] (O : ValuationSubring K) (P : ValuationSubring F)
  (f : K →+* F) (hf : RespectsValuationRing O P f)

include hf in
theorem map_mem_nonunits_iff (x : K) : f x ∈ P.nonunits ↔ x ∈ O.nonunits := by
  rw [P.mem_nonunits_iff_or, O.mem_nonunits_iff_or, ← map_inv₀ f, hf, map_eq_zero]

/-- The induced map of valuation rings. -/
@[expose]
def mapValuationRing : O →+* P :=
  (f.comp O.subtype).codRestrict P.toSubring (fun x => (hf x).mpr x.property)

@[simp] theorem coe_mapValuationRing (x : O) :
    (mapValuationRing O P f hf x : F) = f (x : K) := rfl

/-- The induced map of residue fields. -/
@[expose]
def mapResidue : Residue O →+* Residue P :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O)
    ((IsLocalRing.residue P).comp (mapValuationRing O P f hf)) (by
      intro x hx
      apply (IsLocalRing.residue_eq_zero_iff _).mpr
      apply P.coe_mem_nonunits_iff.mp
      exact (map_mem_nonunits_iff O P f hf (x : K)).mpr (O.coe_mem_nonunits_iff.mpr hx))

@[simp] theorem mapResidue_residue (x : O) :
    mapResidue O P f hf (IsLocalRing.residue O x) =
      IsLocalRing.residue P (mapValuationRing O P f hf x) := rfl

/-- An ordered valued-field embedding induces a strictly monotone
map between the two residue fields in their quotient orders. -/
theorem mapResidue_strictMono [LinearOrder K] [IsStrictOrderedRing K]
    [LinearOrder F] [IsStrictOrderedRing F] (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (hmono : StrictMono f) :
    letI := residueLinearOrder O hO
    letI := residueLinearOrder P hP
    StrictMono (mapResidue O P f hf) := by
  intro r s h
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := O) r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective (R := O) s
  rw [mapResidue_residue, mapResidue_residue, residue_lt_residue_iff P hP]
  obtain ⟨hxy, hne⟩ := (residue_lt_residue_iff O hO).mp h
  exact ⟨hmono hxy, fun he => hne ((mapResidue O P f hf).injective he)⟩

theorem mapRV_residueRV (r : Residue O) :
    mapRV O P f hf (residueRV O r) = residueRV P (mapResidue O P f hf r) := by
  by_cases hr : r = 0
  · rw [hr, map_zero, residueRV_zero, residueRV_zero, mapRV_zero]
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective r
  have hres : IsLocalRing.residue P (mapValuationRing O P f hf x) ≠ 0 := by
    rw [← mapResidue_residue, hx, map_ne_zero]
    exact hr
  rw [← hx, residueRV_residue_of_ne_zero O x (hx.trans_ne hr),
    mapRV_rv, mapResidue_residue, residueRV_residue_of_ne_zero P _ hres, coe_mapValuationRing]

theorem mapRV_in_residue_iff (t : RV0 O) :
    mapRV O P f hf t ∈ Set.range (residueRV P) ↔ t ∈ Set.range (residueRV O) := by
  rw [range_residueRV, range_residueRV]
  change mapRV O P f hf t = 0 ∨ unsignedValue P (mapRV O P f hf t) = 1 ↔
    t = 0 ∨ unsignedValue O t = 1
  rw [mapRV_value_one_iff]
  exact or_congr_left (by
    rw [← mapRV_zero O P f hf]
    exact (mapRV O P f hf).injective.eq_iff)

theorem rvResidue_mapRV (t : RV0 O) :
    rvResidue P (mapRV O P f hf t) = mapResidue O P f hf (rvResidue O t) := by
  by_cases ht : t ∈ Set.range (residueRV O)
  · obtain ⟨r, rfl⟩ := ht
    rw [mapRV_residueRV, rvResidue_residueRV, rvResidue_residueRV]
  · rw [rvResidue_eq_zero_of_not_mem_range O ht, map_zero]
    exact rvResidue_eq_zero_of_not_mem_range P ((mapRV_in_residue_iff O P f hf t).not.mpr ht)

/-- Reductions of compatible field functions commute with the induced
residue map. This applies to the named continuous symbols in Ax. 8. -/
theorem mapResidue_commutes_of_matching {n : ℕ}
    (g : (Fin n → K) → K) (g' : (Fin n → F) → F)
    (gO : (Fin n → Residue O) → Residue O) (gP : (Fin n → Residue P) → Residue P)
    (hg : ∀ x, f (g x) = g' (f ∘ x))
    (hO : ∀ a : Fin n → O, ∃ h : g (fun i => (a i : K)) ∈ O,
      IsLocalRing.residue O ⟨g (fun i => (a i : K)), h⟩ = gO (IsLocalRing.residue O ∘ a))
    (hP : ∀ a : Fin n → P, ∃ h : g' (fun i => (a i : F)) ∈ P,
      IsLocalRing.residue P ⟨g' (fun i => (a i : F)), h⟩ = gP (IsLocalRing.residue P ∘ a))
    (a : Fin n → Residue O) :
    mapResidue O P f hf (gO a) = gP (mapResidue O P f hf ∘ a) := by
  have lift (i : Fin n) : ∃ b : O, IsLocalRing.residue O b = a i :=
    IsLocalRing.residue_surjective (a i)
  choose b hb using lift
  have hb' : IsLocalRing.residue O ∘ b = a := funext hb
  let bP : Fin n → P := mapValuationRing O P f hf ∘ b
  obtain ⟨hgO, hgo⟩ := hO b
  obtain ⟨hgP, hgp⟩ := hP bP
  let cO : O := ⟨g (fun i => (b i : K)), hgO⟩
  let cP : P := ⟨g' (fun i => (bP i : F)), hgP⟩
  have hc : mapValuationRing O P f hf cO = cP := by
    apply Subtype.ext
    exact hg (fun i => (b i : K))
  have hbP : IsLocalRing.residue P ∘ bP = mapResidue O P f hf ∘ a := by
    funext i
    change IsLocalRing.residue P (mapValuationRing O P f hf (b i)) =
      mapResidue O P f hf (a i)
    rw [← mapResidue_residue, hb]
  rw [hb'] at hgo
  rw [hbP] at hgp
  calc
    _ = mapResidue O P f hf (IsLocalRing.residue O cO) := congrArg _ hgo.symm
    _ = IsLocalRing.residue P (mapValuationRing O P f hf cO) := mapResidue_residue O P f hf cO
    _ = IsLocalRing.residue P cP := congrArg _ hc
    _ = _ := hgp

/-- A compatible residue operation commutes with the induced RV map,
including arguments outside the residue field. -/
theorem mapRV_extendResidueOperation {n : ℕ}
    (g : (Fin n → Residue O) → Residue O) (g' : (Fin n → Residue P) → Residue P)
    (hg : ∀ x, mapResidue O P f hf (g x) = g' (mapResidue O P f hf ∘ x))
    (a : Fin n → RV0 O) :
    mapRV O P f hf (extendResidueOperation O g a) =
      extendResidueOperation P g' (mapRV O P f hf ∘ a) := by
  classical
  by_cases h : ∀ i, a i ∈ Set.range (residueRV O)
  · have h' : ∀ i, (mapRV O P f hf ∘ a) i ∈ Set.range (residueRV P) :=
      fun i => (mapRV_in_residue_iff O P f hf _).mpr (h i)
    rw [extendResidueOperation_of_mem_range O g h, extendResidueOperation_of_mem_range P g' h',
      mapRV_residueRV, hg]
    congr 2
    funext i
    exact (rvResidue_mapRV O P f hf (a i)).symm
  · rw [not_forall] at h
    obtain ⟨i, hi⟩ := h
    rw [extendResidueOperation_off_residue O g ⟨i, hi⟩,
      extendResidueOperation_off_residue P g' ⟨i, (mapRV_in_residue_iff O P f hf _).not.mpr hi⟩,
      mapRV_zero]

end GeneralizedEuler.Section2
