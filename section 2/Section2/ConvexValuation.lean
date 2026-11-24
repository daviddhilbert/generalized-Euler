module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Section2.LeadingTerm

/-! Order facts for the valuation ring in §2.2 and its principal units. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

/-- Convexity in the field order. -/
abbrev IsOrderConvex : Prop := Set.OrdConnected (O : Set K)

/-- Every maximal-ideal element is smaller in absolute value than one. -/
theorem abs_lt_one_of_mem_maximalIdeal (hO : IsOrderConvex O)
    {a : K} (ha : a ∈ O.nonunits) : |a| < 1 := by
  by_contra! h
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact (not_le_of_gt (zero_lt_one : (0 : K) < 1)) (by simpa only [abs_zero] using h)
  have hinv : |a⁻¹| ≤ 1 := by
    rw [abs_inv]
    exact inv_le_one_of_one_le₀ h
  obtain ⟨hl, hr⟩ := abs_le.mp hinv
  have hi : a⁻¹ ∈ O :=
    hO.out (O.neg_mem 1 O.one_mem) O.one_mem ⟨hl, hr⟩
  exact ((O.mem_nonunits_iff_or.mp ha).resolve_left ha0) hi

/-- The principal units lie in the interval used for the clamped field power
in the reviewed proof of §2.2. -/
theorem principalUnit_bounds (hO : IsOrderConvex O)
    {u : Kˣ} (hu : u ∈ O.principalUnitGroup) : 1 / 2 < (u : K) ∧ (u : K) < 2 := by
  have upper {b : Kˣ} (hb : b ∈ O.principalUnitGroup) : (b : K) < 2 := by
    have hm : (b : K) - 1 ∈ O.nonunits :=
      O.mem_nonunits_iff.mpr ((O.mem_principalUnitGroup_iff b).mp hb)
    have h := (abs_lt.mp (abs_lt_one_of_mem_maximalIdeal O hO hm)).2
    exact sub_lt_iff_lt_add.mp h |>.trans_le (by rw [one_add_one_eq_two])
  have hm : (u : K) - 1 ∈ O.nonunits :=
    O.mem_nonunits_iff.mpr ((O.mem_principalUnitGroup_iff u).mp hu)
  have hleft := (abs_lt.mp (abs_lt_one_of_mem_maximalIdeal O hO hm)).1
  have hpos : 0 < (u : K) := by
    simpa only [neg_add_cancel] using (lt_sub_iff_add_lt.mp hleft)
  have hinv : (u : K)⁻¹ < 2 := by
    simpa only [Units.val_inv_eq_inv_val] using upper (O.principalUnitGroup.inv_mem hu)
  have hl : 1 / 2 < (u : K) := by
    rw [one_div, inv_lt_comm₀ (by exact zero_lt_two) hpos]
    exact hinv
  exact ⟨hl, upper hu⟩

/-- A class of a positive field element has only positive representatives. -/
theorem pos_of_rv_eq_rv (hO : IsOrderConvex O) {x y : K}
    (hy : 0 < y) (hxy : rv O x = rv O y) : 0 < x := by
  have hm := (rv_eq_rv_iff O hy.ne').mp hxy
  rw [sub_div, div_self hy.ne'] at hm
  have h := (abs_lt.mp (abs_lt_one_of_mem_maximalIdeal O hO hm)).1
  have hdiv : 0 < x / y := by
    simpa only [neg_add_cancel] using lt_sub_iff_add_lt.mp h
  exact (div_pos_iff.mp hdiv).elim And.left (fun hneg => (hneg.2.not_gt hy).elim)

end GeneralizedEuler.Section2
