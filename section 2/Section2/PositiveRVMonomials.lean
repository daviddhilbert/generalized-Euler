module

public import Section2.RVSplitCoordinates
public import Section2.AffinePullback

/-! Values of the positive monomial lifts used in Lemma 2.29. -/

public section

namespace GeneralizedEuler.Section2

open RVValueSection

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)

theorem isPositiveRV_one : IsPositiveRV O 1 :=
  ⟨⟨1, zero_lt_one⟩, map_one (rv O)⟩

omit [IsStrictOrderedRing K] in
theorem IsPositiveRV.ne_zero {t : RV0 O} (ht : IsPositiveRV O t) : t ≠ 0 := by
  obtain ⟨x, rfl⟩ := ht
  exact (rv_eq_zero_iff O).not.mpr x.property.ne'

theorem IsPositiveRV.mul {s t : RV0 O} (hs : IsPositiveRV O s) (ht : IsPositiveRV O t) :
    IsPositiveRV O (s * t) := by
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  exact ⟨⟨x.val * y.val, mul_pos x.property y.property⟩, map_mul (rv O) x.val y.val⟩

theorem IsPositiveRV.div {s t : RV0 O} (hs : IsPositiveRV O s) (ht : IsPositiveRV O t) :
    IsPositiveRV O (s / t) := by
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  exact ⟨⟨x.val / y.val, div_pos x.property y.property⟩,
    map_div₀ (G₀ := K) (G₀' := RV0 O) (rv O) x.val y.val⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem valueCoordinate_div {s t : RV0 O} (hs : s ≠ 0) (ht : t ≠ 0) :
    valueCoordinate (s / t) = valueCoordinate s / valueCoordinate t := by
  rw [div_eq_mul_inv (G := RV0 O), valueCoordinate_mul hs (inv_ne_zero (G₀ := RV0 O) ht),
    valueCoordinate_inv, div_eq_mul_inv]

theorem valueCoordinate_positiveRV (t : PositiveRV O) :
    valueCoordinate (positiveRVToRV0 O t) = positiveValueMap O t := by
  apply Units.ext
  rw [coe_valueCoordinate (IsPositiveRV.ne_zero O (positiveRVToRV0_pos O t)), positiveValueMap_coe]

private theorem positiveValue_list_prod {I : Type*} (f : I → RV0 O) (hf : ∀ i, IsPositiveRV O (f i))
    (indices : List I) :
    IsPositiveRV O (indices.map f).prod ∧
      valueCoordinate (indices.map f).prod = (indices.map (valueCoordinate ∘ f)).prod := by
  induction indices with
  | nil =>
    refine ⟨isPositiveRV_one O, ?_⟩
    change valueCoordinate (1 : RV0 O) = 1
    simpa only [residueRV_one] using (valueCoordinate_residueRV (O := O) (1 : Residue O))
  | cons i r ih =>
    simp only [List.map_cons, List.prod_cons, Function.comp_apply]
    exact ⟨IsPositiveRV.mul O (hf i) ih.1,
      (valueCoordinate_mul (IsPositiveRV.ne_zero O (hf i)) (IsPositiveRV.ne_zero O ih.1)).trans
        (congrArg (valueCoordinate (f i) * ·) ih.2)⟩

variable {E : Type*} [Field E] {g : E → PositiveField K →* PositiveField K}
  {P : E → RV0 O → RV0 O} (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

set_option linter.style.haveILetI false in
theorem valueCoordinate_positive_power (e : E) {t : RV0 O} (ht : IsPositiveRV O t) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    valueCoordinate (P e t) = (e • Additive.ofMul (valueCoordinate t)).toMul := by
  letI := positiveRVModule O g P hP hzero hone hadd hmul
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  obtain ⟨u, rfl⟩ := exists_positiveRV_of_positive O ht
  let a := Additive.ofMul u
  have hs := positiveRVToRV0_smul O g P hP hzero hone hadd hmul e a
  change positiveRVToRV0 O (e • a).toMul = P e (positiveRVToRV0 O u) at hs
  rw [← hs,
    valueCoordinate_positiveRV, valueCoordinate_positiveRV]
  let v := positiveValueLinearMap O g P hP hzero hone hadd hmul hunit
  have hv := v.map_smul e a
  rw [positiveValueLinearMap_apply, positiveValueLinearMap_apply] at hv
  exact congrArg Additive.toMul hv

set_option linter.style.haveILetI false in
/-- A lifted affine coordinate is positive and maps to the intended
affine value, in the same additive value convention as the manuscript. -/
theorem positive_affine_monomial {m n : ℕ} (coeff : Fin n → Fin m → E)
    (u : Fin n → RV0 O) (hu : ∀ i, IsPositiveRV O (u i))
    (t : Fin m → RV0 O) (ht : ∀ j, IsPositiveRV O (t j)) (i : Fin n) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    let x := u i * (((Finset.univ : Finset (Fin m)).toList).map (fun j => P (coeff i j) (t j))).prod
    IsPositiveRV O x ∧
      Additive.ofMul (valueCoordinate x) =
        affineCoordinates coeff (Additive.ofMul ∘ valueCoordinate ∘ u)
          (Additive.ofMul ∘ valueCoordinate ∘ t) i := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  let f (j : Fin m) := P (coeff i j) (t j)
  let indices := (Finset.univ : Finset (Fin m)).toList
  have h := positiveValue_list_prod O f (fun j => leadingTermPower_pos O (hP (coeff i j)) (ht j)) indices
  change IsPositiveRV O (u i * (indices.map f).prod) ∧
    Additive.ofMul (valueCoordinate (u i * (indices.map f).prod)) = _
  refine ⟨IsPositiveRV.mul O (hu i) h.1, ?_⟩
  rw [valueCoordinate_mul (IsPositiveRV.ne_zero O (hu i)) (IsPositiveRV.ne_zero O h.1), h.2]
  apply Additive.toMul.injective
  rw [affineCoordinates, toMul_add, toMul_sum, Finset.prod_map_toList]
  change valueCoordinate (u i) * Finset.univ.prod (valueCoordinate ∘ f) =
    valueCoordinate (u i) * ∏ j, (coeff i j • Additive.ofMul (valueCoordinate (t j))).toMul
  apply congrArg (valueCoordinate (u i) * ·)
  apply Finset.prod_congr rfl
  intro j _
  exact valueCoordinate_positive_power O hP hzero hone hadd hmul hunit (coeff i j) (ht j)

end GeneralizedEuler.Section2
