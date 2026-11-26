module

public import Section5.UnaryTranslationPullback

/-! Describe all labels after one unary focus step. A nonzero focus
fiber gives the elementary multiplier, while the zero fiber and the
complement keep their old leading term. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K) {R : Type*}

theorem unary_translation_labels (A : Set (K × R)) (T : RelativeTranslation O (id : R → R))
    (full : IsUnaryPullback O A) (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t) :
    unaryMixedLabel O '' (recodeUnaryTranslation O T '' A) =
      {u : RV0 O × (R × RV0 O) | (u.2.2,u.2.1) ∈ unaryMixedLabel O '' A ∧
        (((u.2.1,u.2.2) ∈ T.locus ∧ u.2.2 ≠ 0 ∧ unsignedValue O u.1 < unsignedValue O u.2.2) ∨
          (((u.2.1,u.2.2) ∉ T.locus ∨ u.2.2 = 0) ∧ u.1 = u.2.2))} := by
  classical
  have offset (r t) : T.offset r t = if (r,t) ∈ T.locus then T.focus r t else 0 := rfl
  have zero (r : R) : T.offset r 0 = 0 := by
    rw [offset]
    by_cases h : (r,0) ∈ T.locus
    · rw [ite_eq_left h]
      exact (rv_eq_zero_iff O).1 (valid _ _ h)
    · rw [ite_eq_right h]
  ext u
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    let t := rv O x.1
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    change (((x.2,t) ∈ T.locus ∧ t ≠ 0 ∧ unsignedValue O (rv O (x.1-T.offset x.2 t)) < unsignedValue O t) ∨
      (((x.2,t) ∉ T.locus ∨ t = 0) ∧ rv O (x.1-T.offset x.2 t) = t))
    by_cases h : (x.2,t) ∈ T.locus
    · by_cases hz : t = 0
      · exact Or.inr ⟨Or.inr hz,by rw [hz,zero,sub_zero]; exact hz⟩
      · refine Or.inl ⟨h,hz,?_⟩
        rw [offset,ite_eq_left h,unsignedValue_rv]
        apply (RelativeTranslation.focus_translation_iff (O := O) hz (valid _ _ h)).1
        rw [sub_add_cancel]
    · exact Or.inr ⟨Or.inl h,by rw [offset,ite_eq_right h,sub_zero]⟩
  · rintro ⟨⟨x,hx,label⟩,case⟩
    obtain ⟨y,lead⟩ := rv_surjective O u.1
    let r := u.2.1
    let t := u.2.2
    let a := y + T.offset r t
    have old : rv O a = t := by
      rcases case with ⟨inLocus,nz,small⟩ | ⟨outside,same⟩
      · change rv O (y + T.offset r t) = t
        rw [offset,ite_eq_left inLocus]
        apply (RelativeTranslation.focus_translation_iff (O := O) nz (valid _ _ inLocus)).2
        rw [← unsignedValue_rv,lead]
        exact small
      · change rv O (y + T.offset r t) = t
        have noOffset : T.offset r t = 0 := by
          rcases outside with outside | z
          · rw [offset,ite_eq_right outside]
          · change t = 0 at z
            rw [z,zero]
        rw [noOffset,add_zero,lead,same]
    have h : unaryMixedLabel O x = unaryMixedLabel O (a,r) := label.trans (Prod.ext old.symm rfl)
    have mem := full x hx (a,r) h
    refine ⟨recodeUnaryTranslation O T (a,r),⟨(a,r),mem,rfl⟩,?_⟩
    change (rv O (a-T.offset r (rv O a)),(r,rv O a)) = u
    rw [old]
    exact Prod.ext ((congrArg (rv O) (add_sub_cancel_right y (T.offset r t))).trans lead) rfl

end GeneralizedEuler.Section5
