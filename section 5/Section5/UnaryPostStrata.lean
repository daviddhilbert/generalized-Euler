module

public import Section5.UnaryLabelOrder

/-! Split each post-translation degree according to whether the old
label belongs to the translated locus. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K) {I : Type} {m : ℕ}

@[expose] def appendUnaryLabelSet (D : Set (Fin m → RV0 O))
    (test : (Fin m → RV0 O) → RV0 O → Prop) : Set (Fin (m+1) → RV0 O) :=
  let idx : Fin (m+1) ≃ Fin m ⊕ Fin 1 := finSumFinEquiv.symm
  {w | w ∘ blowupOldIndices idx ∈ D ∧ test (w ∘ blowupOldIndices idx) (w (blowupExtraIndex idx))}

@[expose] def unarySelectedLabels (A : Set (K × (I → RV0 O))) (idx : Fin m ≃ Fin 1 ⊕ I)
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O))) : Set (Fin m → RV0 O) :=
  {t ∈ reindexedUnaryLabels O A idx | t ∘ idx.symm ∈ translatedUnaryCut O T}

theorem unarySelectedLabel_nonzero {A : Set (K × (I → RV0 O))} (idx : Fin m ≃ Fin 1 ⊕ I)
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t)
    {t : Fin m → RV0 O} (h : t ∈ unarySelectedLabels O A idx T) : t (idx.symm (.inl 0)) ≠ 0 :=
  ((unary_offset_ne_zero_iff O T valid _ _).1 h.2).2

theorem unary_post_zero_strata (A : Set (K × (I → RV0 O))) (idx : Fin m ≃ Fin 1 ⊕ I)
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (full : IsUnaryPullback O A) (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t) :
    let D₀ := {t ∈ reindexedUnaryLabels O A idx | t (idx.symm (.inl 0)) = 0}
    let D := unarySelectedLabels O A idx T
    {w ∈ reindexedUnaryLabels O (encodedUnaryImage O A T) (unaryPostIndex idx) |
      w ((unaryPostIndex idx).symm (.inl 0)) = 0} =
      appendUnaryLabelSet O D₀ (fun _ b => b = 0) ∪ appendUnaryLabelSet O D (fun _ b => b = 0) := by
  intro D₀ D
  ext w
  let j := idx.symm (.inl 0)
  let k : Fin (m+1) ≃ Fin m ⊕ Fin 1 := finSumFinEquiv.symm
  let t := w ∘ blowupOldIndices k
  let b := w (blowupExtraIndex k)
  have h := reindexed_unary_post_labels O A idx T full valid w
  have ha : w ((unaryPostIndex idx).symm (.inl 0)) = b := congrArg w (unaryPostIndex_active idx)
  change (w ∈ reindexedUnaryLabels O (encodedUnaryImage O A T) (unaryPostIndex idx) ∧
      w ((unaryPostIndex idx).symm (.inl 0)) = 0) ↔
    (t ∈ D₀ ∧ b = 0) ∨ (t ∈ D ∧ b = 0)
  dsimp only at h
  rw [h,ha]
  constructor
  · rintro ⟨⟨hD,⟨hc,_⟩ | ⟨_,eq⟩⟩,hz⟩
    · exact Or.inr ⟨⟨hD,hc⟩,hz⟩
    · exact Or.inl ⟨⟨hD,eq.symm.trans hz⟩,hz⟩
  · rintro (⟨⟨hD,hz⟩,hb⟩ | ⟨hd,hb⟩)
    · have no : t ∘ idx.symm ∉ translatedUnaryCut O T := fun hc =>
        unarySelectedLabel_nonzero O idx T valid (⟨hD,hc⟩ : t ∈ D) hz
      exact ⟨⟨hD,Or.inr ⟨no,hb.trans hz.symm⟩⟩,hb⟩
    · have hn := unarySelectedLabel_nonzero O idx T valid hd
      refine ⟨⟨hd.1,Or.inl ⟨hd.2,?_⟩⟩,hb⟩
      rw [show w (blowupExtraIndex k) = 0 from hb,map_zero]
      exact pos_iff_ne_zero.2 ((map_ne_zero _).2 hn)

theorem unary_post_positive_strata (A : Set (K × (I → RV0 O))) (idx : Fin m ≃ Fin 1 ⊕ I)
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (full : IsUnaryPullback O A) (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t) :
    let j := idx.symm (.inl 0)
    let D := unarySelectedLabels O A idx T
    let R := {t ∈ reindexedUnaryLabels O A idx | t j ≠ 0} \ D
    {w ∈ reindexedUnaryLabels O (encodedUnaryImage O A T) (unaryPostIndex idx) |
      w ((unaryPostIndex idx).symm (.inl 0)) ≠ 0} =
      appendUnaryLabelSet O R (fun t b => b = t j) ∪
      appendUnaryLabelSet O D (fun t b => unsignedValue O b < unsignedValue O (t j) ∧ b ≠ 0) := by
  intro j D R
  ext w
  let k : Fin (m+1) ≃ Fin m ⊕ Fin 1 := finSumFinEquiv.symm
  let t := w ∘ blowupOldIndices k
  let b := w (blowupExtraIndex k)
  have h := reindexed_unary_post_labels O A idx T full valid w
  have ha : w ((unaryPostIndex idx).symm (.inl 0)) = b := congrArg w (unaryPostIndex_active idx)
  change (w ∈ reindexedUnaryLabels O (encodedUnaryImage O A T) (unaryPostIndex idx) ∧
      w ((unaryPostIndex idx).symm (.inl 0)) ≠ 0) ↔
    (t ∈ R ∧ b = t j) ∨ (t ∈ D ∧ unsignedValue O b < unsignedValue O (t j) ∧ b ≠ 0)
  dsimp only at h
  rw [h,ha]
  constructor
  · rintro ⟨⟨hD,⟨hc,hv⟩ | ⟨hc,he⟩⟩,hb⟩
    · exact Or.inr ⟨⟨hD,hc⟩,hv,hb⟩
    · exact Or.inl ⟨⟨⟨hD,fun hd => hb (he.trans hd)⟩,fun hd => hc hd.2⟩,he⟩
  · rintro (⟨⟨⟨hD,hz⟩,hno⟩,he⟩ | ⟨hd,hv,hb⟩)
    · exact ⟨⟨hD,Or.inr ⟨fun hc => hno ⟨hD,hc⟩,he⟩⟩,fun he' => hz (he.symm.trans he')⟩
    · exact ⟨⟨hd.1,Or.inl ⟨hd.2,hv⟩⟩,hb⟩

end GeneralizedEuler.Section5
