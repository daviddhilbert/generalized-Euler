module

public import Section2.ValuativeDisc
public import Mathlib.Tactic.Ring

/-! The quotients RVγ in Notation 2.34, with the radius written in the
multiplicative convention. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

private theorem value_one_of_sub_one_lt {x : K} {r : O.ValueGroup} (hr : r ≤ 1)
    (hx : O.valuation (x - 1) < r) : O.valuation x = 1 := by
  have h : O.valuation (x - 1) < O.valuation 1 := by simpa using hx.trans_le hr
  exact (O.valuation.map_eq_of_sub_lt h).trans (map_one _)

/-- The subgroup 1 + Mγ for a finite nonnegative additive radius γ. -/
@[expose]
def higherPrincipalUnits (r : O.ValueGroup) (hr : r ≠ 0) (hr₁ : r ≤ 1) :
    Subgroup Kˣ where
  carrier := {u | O.valuation ((u : K) - 1) < r}
  one_mem' := by simpa using pos_iff_ne_zero.mpr hr
  mul_mem' := by
    intro x y hx hy
    change O.valuation ((x : K) - 1) < r at hx
    change O.valuation ((y : K) - 1) < r at hy
    change O.valuation ((x : K) * y - 1) < r
    have h : (x : K) * y - 1 = ((x : K) - 1) * y + ((y : K) - 1) := by ring
    rw [h]
    refine (O.valuation.map_add _ _).trans_lt (max_lt ?_ hy)
    rwa [map_mul, value_one_of_sub_one_lt O hr₁ hy, mul_one]
  inv_mem' := by
    intro x hx
    change O.valuation ((x : K) - 1) < r at hx
    change O.valuation (((x⁻¹ : Kˣ) : K) - 1) < r
    rw [Units.val_inv_eq_inv_val]
    have h : (x : K)⁻¹ - 1 = -((x : K) - 1) * (x : K)⁻¹ := by
      rw [neg_sub, sub_mul, one_mul, mul_inv_cancel₀ x.ne_zero]
    rwa [h, map_mul, O.valuation.map_neg, map_inv₀, value_one_of_sub_one_lt O hr₁ hx,
      inv_one, mul_one]

abbrev HigherRV0 (r : O.ValueGroup) (hr : r ≠ 0) (hr₁ : r ≤ 1) :=
  WithZero (Kˣ ⧸ higherPrincipalUnits O r hr hr₁)

def higherRv (r : O.ValueGroup) (hr : r ≠ 0) (hr₁ : r ≤ 1) :
    K →*₀ HigherRV0 O r hr hr₁ :=
  unitQuotientWithZero (higherPrincipalUnits O r hr hr₁)

@[simp]
theorem higherRv_coe_unit {r : O.ValueGroup} (hr : r ≠ 0) (hr₁ : r ≤ 1) (x : Kˣ) :
    higherRv O r hr hr₁ (x : K) =
      (QuotientGroup.mk' (higherPrincipalUnits O r hr hr₁) x : HigherRV0 O r hr hr₁) :=
  unitQuotientWithZero_coe_unit (higherPrincipalUnits O r hr hr₁) x

theorem higherRv_eq_zero_iff {r : O.ValueGroup} (hr : r ≠ 0) (hr₁ : r ≤ 1) {x : K} :
    higherRv O r hr hr₁ x = 0 ↔ x = 0 :=
  unitQuotientWithZero_eq_zero_iff (higherPrincipalUnits O r hr hr₁)

theorem higherRv_surjective {r : O.ValueGroup} (hr : r ≠ 0) (hr₁ : r ≤ 1) :
    Function.Surjective (higherRv O r hr hr₁) :=
  unitQuotientWithZero_surjective (higherPrincipalUnits O r hr hr₁)

/-- The nonzero fiber of rvγ is the open disc of radius γ plus the
value of any of its representatives in the additive convention. -/
theorem higherRv_eq_iff {r : O.ValueGroup} (hr : r ≠ 0) (hr₁ : r ≤ 1) {x y : K}
    (hy : y ≠ 0) :
    higherRv O r hr hr₁ x = higherRv O r hr hr₁ y ↔
      x ∈ openDisc O y (r * O.valuation y) := by
  change _ ↔ O.valuation (x - y) < r * O.valuation y
  have hypos : 0 < O.valuation y := pos_iff_ne_zero.mpr ((map_ne_zero O.valuation).mpr hy)
  by_cases hx : x = 0
  · subst x
    rw [map_zero (higherRv O r hr hr₁), eq_comm, higherRv_eq_zero_iff, zero_sub, O.valuation.map_neg]
    exact iff_of_false hy (not_lt.mpr (mul_le_of_le_one_left hypos.le hr₁))
  let u := Units.mk0 x hx
  let v := Units.mk0 y hy
  let q := QuotientGroup.mk' (higherPrincipalUnits O r hr hr₁)
  change higherRv O r hr hr₁ (u : K) = higherRv O r hr hr₁ (v : K) ↔
    O.valuation ((u : K) - (v : K)) < r * O.valuation (v : K)
  rw [higherRv_coe_unit, higherRv_coe_unit, WithZero.coe_inj]
  have hquot : q u = q v ↔ u / v ∈ higherPrincipalUnits O r hr hr₁ := by
    rw [← div_eq_one, ← map_div q, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  rw [hquot]
  change O.valuation (((u / v : Kˣ) : K) - 1) < r ↔ _
  rw [Units.val_div_eq_div_val, ← div_self v.ne_zero, ← sub_div, map_div₀]
  exact div_lt_iff₀ hypos

/-- At a positive additive radius γ, the rvγ fibers on the closed
parent of a nonzero fiber are exactly its maximal open children. -/
theorem higherRv_eq_iff_openChild {r : O.ValueGroup} (hr : r ≠ 0) (hr₁ : r < 1)
    {a : K} (ha : a ≠ 0) (x y : closedDisc O a (r * O.valuation a)) :
    higherRv O r hr hr₁.le (x : K) = higherRv O r hr hr₁.le (y : K) ↔
      (x : K) ∈ openDisc O (y : K) (r * O.valuation a) := by
  have hapos : 0 < O.valuation a := pos_iff_ne_zero.mpr ((map_ne_zero O.valuation).mpr ha)
  have hy : O.valuation ((y : K) - a) ≤ r * O.valuation a := y.property
  have hradius : r * O.valuation a < O.valuation a := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hr₁ hapos
  have hvalue := O.valuation.map_eq_of_sub_lt (hy.trans_lt hradius)
  have hyne : (y : K) ≠ 0 := fun hy0 => hapos.ne' (hvalue.symm.trans (by simp [hy0]))
  rw [higherRv_eq_iff O hr hr₁.le hyne, hvalue]

end GeneralizedEuler.Section2
