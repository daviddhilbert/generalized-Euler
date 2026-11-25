module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! The order-field change of charts used in Definition 2.36. The
epsilon-delta definition applies to non-Archimedean ordered fields. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Differentiability using punctured neighborhoods in the order topology. -/
def HasOrderDerivativeAt (f : K → K) (x d : K) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ h : K, h ≠ 0 → |h| < δ →
    |(f (x + h) - f x) / h - d| < ε

theorem HasOrderDerivativeAt.unique {f : K → K} {x d e : K}
    (hd : HasOrderDerivativeAt f x d) (he : HasOrderDerivativeAt f x e) : d = e := by
  by_contra hne
  have hpos : 0 < |d - e| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ₁, hδ₁, h₁⟩ := hd (|d - e| / 2) (div_pos hpos zero_lt_two)
  obtain ⟨δ₂, hδ₂, h₂⟩ := he (|d - e| / 2) (div_pos hpos zero_lt_two)
  let h := min δ₁ δ₂ / 2
  have hh : 0 < h := div_pos (lt_min hδ₁ hδ₂) zero_lt_two
  have hsmall : |h| < min δ₁ δ₂ :=
    (abs_of_pos hh).trans_lt (div_lt_self (lt_min hδ₁ hδ₂) one_lt_two)
  have hd' := h₁ h hh.ne' (hsmall.trans_le (min_le_left _ _))
  have he' := h₂ h hh.ne' (hsmall.trans_le (min_le_right _ _))
  let q := (f (x + h) - f x) / h
  have hb : |d - e| ≤ |q - d| + |q - e| := by
    simpa only [abs_sub_comm d q] using abs_sub_le d q e
  have hs : |q - d| + |q - e| < |d - e| := by
    simpa only [add_halves] using add_lt_add hd' he'
  exact (hb.trans_lt hs).false

/-- Under affine source and target changes the coordinate derivative
is multiplied by the ratio of the target and source scales. -/
theorem HasOrderDerivativeAt.affine_change {f : K → K} {x d : K}
    (hf : HasOrderDerivativeAt f x d) (a b p q : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    HasOrderDerivativeAt (fun z => q + b * f ((z - p) / a)) (p + a * x) ((b / a) * d) := by
  intro ε hε
  have hc : 0 < |b / a| := abs_pos.mpr (div_ne_zero hb ha)
  obtain ⟨δ, hδ, H⟩ := hf (ε / |b / a|) (div_pos hε hc)
  refine ⟨δ * |a|, mul_pos hδ (abs_pos.mpr ha), ?_⟩
  intro h hh hlt
  have hk : |h / a| < δ := by
    rw [abs_div]
    exact (div_lt_iff₀ (abs_pos.mpr ha)).mpr hlt
  have H' := H (h / a) (div_ne_zero hh ha) hk
  have htop : (p + a * x + h - p) / a = x + h / a := by
    field_simp
    ring
  have hbase : (p + a * x - p) / a = x := by
    field_simp
    ring
  change |(q + b * f ((p + a * x + h - p) / a) -
    (q + b * f ((p + a * x - p) / a))) / h - (b / a) * d| < ε
  rw [htop, hbase]
  have hdiff :
      (q + b * f (x + h / a) - (q + b * f x)) / h - (b / a) * d =
        (b / a) * ((f (x + h / a) - f x) / (h / a) - d) := by
    field_simp
    ring
  rw [hdiff, abs_mul]
  have H'' := (lt_div_iff₀ hc).mp H'
  simpa only [mul_comm] using H''

omit [IsStrictOrderedRing K] in
/-- The factor converting a coordinate derivative to an affine direction
cancels the change of coordinates. -/
theorem torsor_derivative_scale_invariant (s t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((s / b) / (t / a)) * ((b / a) * d) = (s / t) * d := by
  by_cases ht : t = 0
  · simp [ht]
  field_simp

end GeneralizedEuler.Section2
