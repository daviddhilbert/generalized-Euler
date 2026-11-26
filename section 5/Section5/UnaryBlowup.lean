module

public import Section2.DiscCodes

/-! A centered unary lift of the elementary blowup. The tag includes the
zero multiplier, which is responsible for the lower-degree piece. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- The field coordinate and multiplier of the lift of a single blown-up
leading-term label. The multiplier's value is less than one in the
multiplicative order. -/
abbrev BlownUpFiber (t : RV0 O) :=
  {p : K × RV0 O // unsignedValue O p.2 < 1 ∧ rv O p.1 = p.2 * t}

private theorem multiplier_lt_one {c y : K} (hc : c ≠ 0) :
    unsignedValue O (rv O (y / c)) < 1 ↔ O.valuation y < O.valuation c := by
  rw [unsignedValue_rv, map_div₀]
  exact div_lt_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero O.valuation).mpr hc))

private theorem multiplier_label {c y : K} (hc : c ≠ 0) :
    rv O y = rv O (y / c) * rv O c := by
  rw [← map_mul, div_mul_cancel₀ _ hc]

/-- Translation by a chosen focus lifts the unary blowup. The retained
old RV label is fixed, and the new multiplier is determined by the
translated field coordinate. -/
noncomputable def liftUnaryBlowup (c : K) (hc : c ≠ 0) :
    {x : K // rv O x = rv O c} ≃ BlownUpFiber O (rv O c) where
  toFun x := by
    refine ⟨(x.val - c, rv O ((x.val - c) / c)), ?_, multiplier_label O hc⟩
    exact (multiplier_lt_one O hc).2 ((rv_eq_rv_iff_valuation O hc).1 x.property)
  invFun p := by
    refine ⟨p.val.1 + c, (rv_eq_rv_iff_valuation O hc).2 ?_⟩
    rw [add_sub_cancel_right]
    have h := congrArg (unsignedValue O) p.property.2
    simp only [unsignedValue_rv, map_mul] at h
    rw [h]
    have hpos : 0 < O.valuation c := pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hc)
    simpa only [one_mul] using mul_lt_mul_of_pos_right p.property.1 hpos
  left_inv x := by
    apply Subtype.ext
    exact sub_add_cancel x.val c
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext (add_sub_cancel_right p.val.1 c) ?_
    change rv O ((p.val.1 + c - c) / c) = p.val.2
    rw [add_sub_cancel_right, map_div₀]
    exact (div_eq_iff (G₀ := RV0 O) ((rv_eq_zero_iff O).not.mpr hc)).2 p.property.2

theorem liftUnaryBlowup_apply_value (c : K) (hc : c ≠ 0)
    (x : {x : K // rv O x = rv O c}) :
    (liftUnaryBlowup O c hc x).val = (x.val-c,rv O ((x.val-c)/c)) := by
  unfold liftUnaryBlowup
  rfl

theorem blowup_zero_multiplier_iff {t : RV0 O} (ht : t ≠ 0) (p : BlownUpFiber O t) :
    p.val.2 = 0 ↔ p.val.1 = 0 := by
  rw [← rv_eq_zero_iff O, p.property.2, mul_eq_zero, or_iff_left ht]

end GeneralizedEuler.Section5
