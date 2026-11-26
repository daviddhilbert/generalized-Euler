module

public import Section5.DefinablePairedCenterChains

/-! On each final label fiber a unary focus chain is one translation.
The inverse image of a nonpoint label fiber is a full open disc. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {cert : ∀ I : Type, RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)) → Prop}
  {I J : Type} {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))} {e : A ≃ B}

theorem EncodedFocusChain.on_label_fiber (chain : EncodedFocusChain O cert A B e) :
    ∀ x y : A, unaryMixedLabel O (e x).val = unaryMixedLabel O (e y).val →
      unaryMixedLabel O x.val = unaryMixedLabel O y.val ∧ (e y).val.1 - (e x).val.1 = y.val.1 - x.val.1 := by
  induction chain with
  | nil A => exact fun _ _ h => ⟨h,rfl⟩
  | @cons I J A T valid defT B tail next ih =>
    intro x y same
    let g := encodedUnaryStep O A T
    obtain ⟨eq,field⟩ := ih (g x) (g y) same
    have label := original_label_of_encoded_label O T eq
    have tag : x.val.2 = y.val.2 := congrArg (fun t : RV0 O × (I → RV0 O) => t.2) label
    have lead : rv O x.val.1 = rv O y.val.1 := congrArg Prod.fst label
    refine ⟨label,?_⟩
    change (tail (g y)).val.1 - (tail (g x)).val.1 = y.val.1 - x.val.1
    rw [field]
    change (y.val.1 - T.offset y.val.2 (rv O y.val.1)) - (x.val.1 - T.offset x.val.2 (rv O x.val.1)) = _
    rw [tag,lead,sub_sub_sub_cancel_right]

theorem EncodedFocusChain.label_fiber_openDisc (chain : EncodedFocusChain O cert A B e)
    (full : IsUnaryPullback O B) (x : A) (nz : (e x).val.1 ≠ 0) :
    {u | ∃ y : A, y.val.1 = u ∧ unaryMixedLabel O (e y).val = unaryMixedLabel O (e x).val} =
      openDisc O x.val.1 (O.valuation (e x).val.1) := by
  ext u
  constructor
  · rintro ⟨y,rfl,hy⟩
    obtain ⟨_,diff⟩ := chain.on_label_fiber O x y hy.symm
    have h : O.valuation ((e y).val.1-(e x).val.1) < O.valuation (e x).val.1 :=
      (rv_eq_rv_iff_valuation O nz).1 (congrArg Prod.fst hy)
    rwa [diff] at h
  · intro hu
    let z := ((e x).val.1 + (u-x.val.1),(e x).val.2)
    have shift : z.1 - (e x).val.1 = u-x.val.1 := add_sub_cancel_left _ _
    have label : unaryMixedLabel O z = unaryMixedLabel O (e x).val := by
      refine Prod.ext ((rv_eq_rv_iff_valuation O nz).2 ?_) rfl
      rw [shift]
      exact hu
    have mem := full (e x).val (e x).property z label.symm
    let y : A := e.symm ⟨z,mem⟩
    have hy : e y = ⟨z,mem⟩ := e.apply_symm_apply _
    have same : unaryMixedLabel O (e y).val = unaryMixedLabel O (e x).val := by rw [hy]; exact label
    obtain ⟨_,diff⟩ := chain.on_label_fiber O x y same.symm
    rw [hy] at diff
    change z.1 - (e x).val.1 = y.val.1 - x.val.1 at diff
    rw [shift] at diff
    exact ⟨y,sub_left_inj.1 diff.symm,same⟩

end GeneralizedEuler.Section5
