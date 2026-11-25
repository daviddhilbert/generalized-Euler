module

public import Section2.LeadingTermOrder

/-! The residue field embedded in the RV sort, as in Ax. 4 and Ax. 6. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

abbrev Residue := IsLocalRing.ResidueField O

private theorem residue_ne_zero_iff_value_one (x : O) :
    IsLocalRing.residue O x ≠ 0 ↔ O.valuation (x : K) = 1 :=
  (IsLocalRing.residue_ne_zero_iff_isUnit x).trans (O.valuation_eq_one_iff x)

theorem residue_eq_iff_valuation_sub_lt_one (x y : O) :
    IsLocalRing.residue O x = IsLocalRing.residue O y ↔ O.valuation ((x : K) - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, O.valuation_lt_one_iff]
  rfl

/-- Two representatives of a nonzero residue agree in RV exactly when
their residues agree. -/
theorem rv_eq_rv_iff_residue_eq (x y : O) (hy : IsLocalRing.residue O y ≠ 0) :
    rv O (x : K) = rv O (y : K) ↔ IsLocalRing.residue O x = IsLocalRing.residue O y := by
  have hv := (residue_ne_zero_iff_value_one O y).mp hy
  have hy0 : (y : K) ≠ 0 := by
    intro hy0
    rw [hy0, map_zero] at hv
    exact zero_ne_one hv
  rw [rv_eq_rv_iff_valuation O hy0, hv, residue_eq_iff_valuation_sub_lt_one]

private def residueLift (r : Residue O) : O :=
  Classical.choose (IsLocalRing.residue_surjective r)

private theorem residue_residueLift (r : Residue O) :
    IsLocalRing.residue O (residueLift O r) = r :=
  Classical.choose_spec (IsLocalRing.residue_surjective r)

/-- The residue zero is the RV zero. Every other residue is the leading
term of any of its lifts to the valuation ring. -/
def residueRV (r : Residue O) : RV0 O := by
  classical
  exact if r = 0 then 0 else rv O (residueLift O r : K)

@[simp] theorem residueRV_zero : residueRV O (0 : Residue O) = 0 := by
  simp [residueRV]

theorem residueRV_residue_of_ne_zero (x : O) (hx : IsLocalRing.residue O x ≠ 0) :
    residueRV O (IsLocalRing.residue O x) = rv O (x : K) := by
  classical
  rw [residueRV, ite_eq_right hx]
  exact (rv_eq_rv_iff_residue_eq O _ x hx).mpr (residue_residueLift O _)

theorem residueRV_residue (x : O) :
    residueRV O (IsLocalRing.residue O x) =
      if O.valuation (x : K) = 1 then rv O (x : K) else 0 := by
  classical
  by_cases hx : IsLocalRing.residue O x = 0
  · rw [hx, residueRV_zero, ite_eq_right]
    exact fun h => (residue_ne_zero_iff_value_one O x).mpr h hx
  · rw [ite_eq_left ((residue_ne_zero_iff_value_one O x).mp hx)]
    exact residueRV_residue_of_ne_zero O x hx

theorem unsignedValue_residueRV_of_ne_zero {r : Residue O} (hr : r ≠ 0) :
    unsignedValue O (residueRV O r) = 1 := by
  classical
  rw [residueRV, ite_eq_right hr, unsignedValue_rv, ← residue_ne_zero_iff_value_one,
    residue_residueLift]
  exact hr

theorem residueRV_injective : Function.Injective (residueRV O) := by
  classical
  intro r s h
  by_cases hr : r = 0 <;> by_cases hs : s = 0
  · exact hr.trans hs.symm
  · have hv := unsignedValue_residueRV_of_ne_zero O hs
    rw [← h, hr, residueRV_zero, map_zero] at hv
    exact (zero_ne_one hv).elim
  · have hv := unsignedValue_residueRV_of_ne_zero O hr
    rw [h, hs, residueRV_zero, map_zero] at hv
    exact (zero_ne_one hv).elim
  · rw [residueRV, residueRV, ite_eq_right hr, ite_eq_right hs] at h
    have hs' : IsLocalRing.residue O (residueLift O s) ≠ 0 :=
      (residue_residueLift O s).trans_ne hs
    simpa only [residue_residueLift] using
      (rv_eq_rv_iff_residue_eq O _ _ hs').mp h

theorem range_residueRV :
    Set.range (residueRV O) = {t | t = 0 ∨ unsignedValue O t = 1} := by
  classical
  ext t
  constructor
  · rintro ⟨r, rfl⟩
    rcases eq_or_ne r 0 with rfl | hr
    · exact Or.inl (residueRV_zero O)
    · exact Or.inr (unsignedValue_residueRV_of_ne_zero O hr)
  · rintro (ht | ht)
    · exact ⟨0, (residueRV_zero O).trans ht.symm⟩
    obtain ⟨x, rfl⟩ := rv_surjective O t
    have hx : O.valuation x = 1 := (unsignedValue_rv O x).symm.trans ht
    let y : O := ⟨x, (O.valuation_le_one_iff x).mp hx.le⟩
    refine ⟨IsLocalRing.residue O y, residueRV_residue_of_ne_zero O y ?_⟩
    exact (residue_ne_zero_iff_value_one O y).mpr hx

@[simp] theorem residueRV_one : residueRV O (1 : Residue O) = 1 := by
  have h : IsLocalRing.residue O (1 : O) ≠ 0 := by simp
  simpa only [map_one, OneMemClass.coe_one] using residueRV_residue_of_ne_zero O 1 h

theorem residueRV_mul (r s : Residue O) :
    residueRV O (r * s) = residueRV O r * residueRV O s := by
  by_cases hr : r = 0
  · subst r
    rw [zero_mul, residueRV_zero]
    exact (zero_mul (residueRV O s)).symm
  by_cases hs : s = 0
  · subst s
    rw [mul_zero, residueRV_zero]
    exact (mul_zero (residueRV O r)).symm
  let x := residueLift O r
  let y := residueLift O s
  have hx : IsLocalRing.residue O x = r := residue_residueLift O r
  have hy : IsLocalRing.residue O y = s := residue_residueLift O s
  have hxy : IsLocalRing.residue O (x * y) ≠ 0 := by
    rw [map_mul, hx, hy]
    exact mul_ne_zero hr hs
  rw [← hx, ← hy, ← map_mul, residueRV_residue_of_ne_zero O _ hxy,
    residueRV_residue_of_ne_zero O x (hx.trans_ne hr),
    residueRV_residue_of_ne_zero O y (hy.trans_ne hs)]
  exact map_mul (rv O) (x : K) (y : K)

/-- Reduction on VF, extended by zero outside the valuation ring. -/
def totalResidue (x : K) : Residue O := by
  classical
  exact if h : x ∈ O then IsLocalRing.residue O ⟨x, h⟩ else 0

/-- Reduction on RV₀, extended by zero off the residue field. -/
def rvResidue (t : RV0 O) : Residue O := by
  classical
  exact if h : t ∈ Set.range (residueRV O) then Classical.choose h else 0

theorem rvResidue_eq_zero_of_not_mem_range {t : RV0 O}
    (h : t ∉ Set.range (residueRV O)) : rvResidue O t = 0 := by
  classical
  exact dite_eq_right h

@[simp] theorem rvResidue_residueRV (r : Residue O) : rvResidue O (residueRV O r) = r := by
  classical
  let h : residueRV O r ∈ Set.range (residueRV O) := ⟨r, rfl⟩
  unfold rvResidue
  rw [dite_eq_left h]
  exact residueRV_injective O (Classical.choose_spec h)

theorem rvResidue_rv (x : K) : rvResidue O (rv O x) = totalResidue O x := by
  classical
  by_cases hx : O.valuation x = 1
  · have hxO : x ∈ O := (O.valuation_le_one_iff x).mp hx.le
    let y : O := ⟨x, hxO⟩
    have hres := residueRV_residue_of_ne_zero O y ((residue_ne_zero_iff_value_one O y).mpr hx)
    rw [← hres, rvResidue_residueRV, totalResidue, dite_eq_left hxO]
  · have hv : unsignedValue O (rv O x) ≠ 1 := by simpa only [unsignedValue_rv]
    have htotal : totalResidue O x = 0 := by
      unfold totalResidue
      split
      · exact not_ne_iff.mp (fun h => hx ((residue_ne_zero_iff_value_one O _).mp h))
      · rfl
    rw [htotal]
    by_cases hx0 : x = 0
    · rw [hx0, map_zero, ← residueRV_zero O, rvResidue_residueRV]
    · have hout : rv O x ∉ Set.range (residueRV O) := by
        rw [range_residueRV]
        exact fun h => h.elim (fun hzero => hx0 ((rv_eq_zero_iff O).mp hzero)) hv
      exact dite_eq_right hout

end GeneralizedEuler.Section2
