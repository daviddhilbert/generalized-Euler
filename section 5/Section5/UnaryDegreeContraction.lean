module

public import Section5.UnaryTranslationPullback

/-! In the TCVF grading a unary label has degree zero exactly on the
singleton fibers. A bijection contracting both ways preserves them. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {R T : Type*} {A : Set (K × R)} {B : Set (K × T)}

theorem unary_label_eq_of_zero {x y : K × R} (hz : x.1 = 0)
    (label : unaryMixedLabel O x = unaryMixedLabel O y) : x = y := by
  have same : rv O x.1 = rv O y.1 := congrArg Prod.fst label
  rw [hz,map_zero] at same
  have tags := congrArg (fun u : RV0 O × R => u.2) label
  exact Prod.ext (hz.trans ((rv_eq_zero_iff O).1 same.symm).symm) tags

theorem nonpoint_unary_label {x : K × R} (hx : x.1 ≠ 0)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) :
    ∃ y : K × R, unaryMixedLabel O x = unaryMixedLabel O y ∧ y ≠ x := by
  let y := (x.1 + eps*x.1,x.2)
  have hr : O.valuation x.1 ≠ 0 := (map_ne_zero _).2 hx
  have value : O.valuation (y.1-x.1) < O.valuation x.1 := by
    change O.valuation (x.1 + eps*x.1 - x.1) < O.valuation x.1
    rw [add_comm x.1,add_sub_cancel_right,map_mul]
    simpa only [one_mul] using mul_lt_mul_of_pos_right small (pos_iff_ne_zero.2 hr)
  refine ⟨y,Prod.ext ((rv_eq_rv_iff_valuation O hx).2 value).symm rfl,?_⟩
  intro eq
  have same : x.1 + eps*x.1 = x.1 := congrArg Prod.fst eq
  exact mul_ne_zero he hx (add_left_cancel (same.trans (add_zero _).symm))

private theorem contracted_zero_forward (e : A ≃ B) (fullB : IsUnaryPullback O B)
    (backward : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e.symm)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (x : A) (hx : x.val.1 = 0) :
    (e x).val.1 = 0 := by
  by_contra hf
  obtain ⟨y,label,ne⟩ := nonpoint_unary_label O hf he small
  let z : B := ⟨y,fullB (e x).val (e x).property y label⟩
  have old := backward (e x) z label
  change unaryMixedLabel O (e.symm (e x)).val = unaryMixedLabel O (e.symm z).val at old
  rw [e.symm_apply_apply] at old
  have eq : x = e.symm z := Subtype.ext (unary_label_eq_of_zero O hx old)
  exact ne (congrArg Subtype.val (e.symm_apply_eq.1 eq.symm))

theorem mutual_unary_contraction_preserves_degree (e : A ≃ B)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e)
    (backward : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e.symm)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (x : A) :
    x.val.1 = 0 ↔ (e x).val.1 = 0 := by
  refine ⟨contracted_zero_forward O e fullB backward he small x,?_⟩
  intro h
  simpa only [Equiv.symm_apply_apply] using
    contracted_zero_forward O e.symm fullA forward he small (e x) h

end GeneralizedEuler.Section5
