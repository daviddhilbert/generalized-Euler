module

public import Section5.PairedConjugateGraph

/-! After each unary step, represent the old tag and appended leading
term by variables indexed by a finite sum. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

@[expose] def unaryTagAppend {I : Type} : ((I → RV0 O) × RV0 O) ≃ (I ⊕ Unit → RV0 O) where
  toFun t := Sum.elim t.1 (fun _ => t.2)
  invFun t := (t ∘ Sum.inl,t (.inr ()))
  left_inv _ := rfl
  right_inv t := by
    funext i
    rcases i with i | ⟨⟩ <;> rfl

section Reindex

variable {R T : Type*} (e : R ≃ T) (A : Set (K × R))

@[expose] def reindexUnaryPoint : K × R ≃ K × T := (Equiv.refl K).prodCongr e

@[expose] def reindexUnaryImage : A ≃ reindexUnaryPoint e '' A :=
  Equiv.Set.image _ _ (reindexUnaryPoint e).injective

omit [Field K] in
theorem reindexUnaryImage_apply (x : A) :
    (reindexUnaryImage e A x).val = (x.val.1,e x.val.2) := rfl

theorem reindexUnaryPoint_label_eq (x y : K × R) :
    unaryMixedLabel O (reindexUnaryPoint e x) = unaryMixedLabel O (reindexUnaryPoint e y) ↔
      unaryMixedLabel O x = unaryMixedLabel O y := by
  constructor
  · intro h
    exact Prod.ext (congrArg (fun t : RV0 O × T => t.1) h)
      (e.injective (congrArg (fun t : RV0 O × T => t.2) h))
  · intro h
    exact Prod.ext (congrArg (fun t : RV0 O × R => t.1) h) (congrArg (fun t : RV0 O × R => e t.2) h)

theorem reindexUnaryImage_is_pullback (full : IsUnaryPullback O A) :
    IsUnaryPullback O (reindexUnaryPoint e '' A) := by
  rintro _ ⟨x,hx,rfl⟩ y labels
  obtain ⟨z,rfl⟩ := (reindexUnaryPoint e).surjective y
  exact ⟨z,full x hx z ((reindexUnaryPoint_label_eq O e x z).1 labels),rfl⟩

end Reindex

section Transport

variable {R R' T T' : Type*} {A : Set (K × R)} {B : Set (K × T)}
  (p : R ≃ R') (q : T ≃ T') (e : A ≃ B)

@[expose] def reindexUnaryEquiv : (reindexUnaryPoint p '' A) ≃ (reindexUnaryPoint q '' B) :=
  (reindexUnaryImage p A).symm.trans (e.trans (reindexUnaryImage q B))

omit [Field K] in
theorem reindexUnaryEquiv_apply (x : A) :
    reindexUnaryEquiv p q e (reindexUnaryImage p A x) = reindexUnaryImage q B (e x) := by
  change reindexUnaryImage q B (e ((reindexUnaryImage p A).symm (reindexUnaryImage p A x))) = _
  rw [Equiv.symm_apply_apply]

omit [Field K] in
theorem reindexUnaryEquiv_symm_apply (x : B) :
    (reindexUnaryEquiv p q e).symm (reindexUnaryImage q B x) = reindexUnaryImage p A (e.symm x) := by
  change reindexUnaryImage p A (e.symm ((reindexUnaryImage q B).symm (reindexUnaryImage q B x))) = _
  rw [Equiv.symm_apply_apply]

theorem reindexUnaryEquiv_contractible
    (h : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e) :
    Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val)
      (reindexUnaryEquiv p q e) := by
  intro x y eq
  obtain ⟨x,rfl⟩ := (reindexUnaryImage p A).surjective x
  obtain ⟨y,rfl⟩ := (reindexUnaryImage p A).surjective y
  change unaryMixedLabel O (reindexUnaryPoint p x.val) = unaryMixedLabel O (reindexUnaryPoint p y.val) at eq
  have same := h x y ((reindexUnaryPoint_label_eq O p x.val y.val).1 eq)
  change unaryMixedLabel O (reindexUnaryEquiv p q e (reindexUnaryImage p A x)).val =
    unaryMixedLabel O (reindexUnaryEquiv p q e (reindexUnaryImage p A y)).val
  rw [reindexUnaryEquiv_apply,reindexUnaryEquiv_apply]
  exact (reindexUnaryPoint_label_eq O q (e x).val (e y).val).2 same

theorem reindexUnaryEquiv_charts (h : UnaryDiscCharts O e) : UnaryDiscCharts O (reindexUnaryEquiv p q e) := by
  intro x nz
  obtain ⟨x,rfl⟩ := (reindexUnaryImage p A).surjective x
  obtain ⟨b,r,f,g,hr,hchart,hf,hsource⟩ := h x nz
  refine ⟨b,r,f,g,hr,hchart,?_,?_⟩
  · intro y eq
    obtain ⟨y,rfl⟩ := (reindexUnaryImage p A).surjective y
    rw [reindexUnaryEquiv_apply]
    exact hf y ((reindexUnaryPoint_label_eq O p y.val x.val).1 eq)
  · intro u hu
    obtain ⟨y,hy,eq⟩ := hsource u hu
    exact ⟨reindexUnaryImage p A y,hy,(reindexUnaryPoint_label_eq O p y.val x.val).2 eq⟩

end Transport

end GeneralizedEuler.Section5
