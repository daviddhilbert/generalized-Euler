module

public import Section3.SliceExceptions
import all Section3.SliceExceptions

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O)

/-- The strict-value case of 3.30 gives a single constant on the entire
projected branch. Reducing its field mean-value identity compares any
two distinct residues, even in a non-Archimedean residue field. -/
theorem ResidueBranch.constant_of_strict_value {B : Set O} {g d : O → K} {c : K}
    (D : ResidueBranch O hO B g d c) (convex : B.OrdConnected)
    (cn : c ≠ 0) (small : ∀ x ∈ B, O.valuation (d x) < O.valuation c) :
    ∀ x ∈ IsLocalRing.residue O '' B, ∀ y ∈ IsLocalRing.residue O '' B, D.residueValue x = D.residueValue y := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  by_cases h : IsLocalRing.residue O x = IsLocalRing.residue O y
  · exact congrArg _ h
  obtain ⟨z,hz,eqn⟩ := D.meanValue x hx y hy h
  have bz := convex.uIcc_subset hx hy hz
  have zs : O.valuation (D.fieldDerivative z : K) < 1 := by
    rw [D.derivative z bz,map_div₀,div_lt_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr cn))]
    exact small z bz
  have zero : IsLocalRing.residue O (D.fieldDerivative z) = 0 := by
    simpa using (residue_eq_iff_valuation_sub_lt_one O (D.fieldDerivative z) 0).mpr (by simpa using zs)
  have sec := residue_secant_eq O h eqn
  rw [zero,D.contracts x hx,D.contracts y hy] at sec
  exact (sub_eq_zero.mp ((div_eq_zero_iff.mp sec).resolve_right (sub_ne_zero.mpr (Ne.symm h)))).symm

end GeneralizedEuler.Section3
