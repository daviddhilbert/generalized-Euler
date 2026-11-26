module

public import Section5.PairedUnaryCharts

/-! Follow a prescribed finite target focus preparation with its paired
source preparation. The final conjugated map contracts both ways. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

universe u

variable {K : Type u} [Field K] (O : ValuationSubring K)

/-- Finite unary focus translations with full retention of the old label. -/
inductive UnaryTranslationChain : {R T : Type u} →
    (A : Set (K × R)) → (B : Set (K × T)) → (A ≃ B) → Prop
  | nil {R : Type u} (A : Set (K × R)) : UnaryTranslationChain A A (Equiv.refl _)
  | cons {R T : Type u} (A : Set (K × R)) (S : RelativeTranslation O (id : R → R))
      (valid : ∀ r t, (r,t) ∈ S.locus → rv O (S.focus r t) = t)
      {B : Set (K × T)} (tail : (recodeUnaryTranslation O S '' A) ≃ B)
      (next : UnaryTranslationChain (recodeUnaryTranslation O S '' A) B tail) :
      UnaryTranslationChain A B ((unaryImageIso O A S).trans tail)

/-- A target chain gives the focus as a point of the target pullback. -/
inductive UnaryTargetFocusChain : {R T : Type u} →
    (A : Set (K × R)) → (B : Set (K × T)) → (A ≃ B) → Prop
  | nil {R : Type u} (A : Set (K × R)) : UnaryTargetFocusChain A A (Equiv.refl _)
  | cons {R T : Type u} (A : Set (K × R)) (C : Set (RV0 O × R)) (focus : RV0 O × R → A)
      (valid : ∀ t ∈ C, unaryMixedLabel O (focus t).val = t)
      {B : Set (K × T)}
      (tail : (recodeUnaryTranslation O (pairedTargetTranslation O C focus) '' A) ≃ B)
      (next : UnaryTargetFocusChain (recodeUnaryTranslation O (pairedTargetTranslation O C focus) '' A) B tail) :
      UnaryTargetFocusChain A B ((unaryImageIso O A (pairedTargetTranslation O C focus)).trans tail)

theorem unaryTargetFocusChain_refines {R T : Type u} {A : Set (K × R)} {B : Set (K × T)} {e : A ≃ B}
    (chain : UnaryTargetFocusChain O A B e) :
    ∀ a b : A, unaryMixedLabel O (e a).val = unaryMixedLabel O (e b).val →
      unaryMixedLabel O a.val = unaryMixedLabel O b.val := by
  induction chain with
  | nil A => exact fun _ _ h => h
  | cons A C focus valid tail next ih =>
    intro a b h
    have h' := ih _ _ h
    exact congrArg (fun q : RV0 O × (_ × RV0 O) => (q.2.2,q.2.1)) h'

/-- Given the prescribed target chain and the inverse contraction to
its final labels, the paired construction produces a source chain.
At every step the source and target pullbacks and source disc charts
are preserved. -/
theorem paired_unary_focus_chain {T T' : Type u} {B : Set (K × T)} {B' : Set (K × T')}
    {h : B ≃ B'} (target : UnaryTargetFocusChain O B B' h) :
    ∀ {R : Type u} {A : Set (K × R)} (e : A ≃ B),
      IsUnaryPullback O A → IsUnaryPullback O B →
      UnaryDiscCharts O e →
      Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e →
      Contractible (fun y : B => unaryMixedLabel O (h y).val) (unaryMixedLabel O ∘ Subtype.val) e.symm →
      ∃ (R' : Type u) (A' : Set (K × R')) (g : A ≃ A'),
        UnaryTranslationChain O A A' g ∧ IsUnaryPullback O A' ∧ IsUnaryPullback O B' ∧
        Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val)
          (g.symm.trans (e.trans h)) ∧
        Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val)
          (g.symm.trans (e.trans h)).symm := by
  induction target with
  | nil B =>
    intro R A e fullA fullB charts forward back
    exact ⟨R,A,Equiv.refl _,.nil A,fullA,fullB,forward,back⟩
  | cons B C focus valid tail next ih =>
    intro R A e fullA fullB charts forward back
    let S := pairedSourceTranslation O e C focus
    let T₁ := pairedTargetTranslation O C focus
    let s := unaryImageIso O A S
    let t := unaryImageIso O B T₁
    let e' := pairedUnaryConjugate O e C focus
    obtain ⟨fa,fb⟩ := paired_unary_step_preserves_pullbacks O e C focus fullA fullB valid
    have charts' := paired_unary_step_preserves_charts O e C focus fullA forward charts
    have forward' := paired_unary_step_contracts O e C focus forward charts valid
    have back' := paired_unary_step_inverse_contracts O e C focus forward charts valid
      (fun y => unaryMixedLabel O (tail y).val) back (unaryTargetFocusChain_refines O next)
    obtain ⟨R',A',g,hg,ha,hb,hf,hback⟩ := ih e' fa fb charts' forward' back'
    have eq : (s.trans g).symm.trans (e.trans (t.trans tail)) = g.symm.trans (e'.trans tail) := by
      apply Equiv.ext
      intro x
      rfl
    refine ⟨R',A',s.trans g,.cons A S (fun _ _ hz => pairedSourceTranslation_focus_lead O e C focus hz)
      g hg,ha,hb,?_⟩
    rw [eq]
    exact ⟨hf,hback⟩

end GeneralizedEuler.Section5
