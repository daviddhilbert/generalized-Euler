module

public import Section5.EncodedTranslationLabels
public import Section5.UnaryLabelObjects
public import Section5.TranslatedBlowupLabels

/-! Use a common coordinate order for post-translation labels and
the tags of the elementary blowup objects. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {I : Type} {m : ℕ}

@[expose] def unaryLabelShuffle : ((Fin 1 ⊕ I) ⊕ Fin 1) ≃ Fin 1 ⊕ (I ⊕ Unit) where
  toFun
    | .inl (.inl _) => .inr (.inr ())
    | .inl (.inr i) => .inr (.inl i)
    | .inr j => .inl j
  invFun
    | .inr (.inr ()) => .inl (.inl 0)
    | .inr (.inl i) => .inl (.inr i)
    | .inl j => .inr j
  left_inv := by
    rintro ((i | i) | i)
    · rw [Subsingleton.elim i (0 : Fin 1)]
    · rfl
    · rfl
  right_inv := by
    rintro (i | (i | ⟨⟩)) <;> rfl

@[expose] def unaryPostIndex (idx : Fin m ≃ Fin 1 ⊕ I) : Fin (m+1) ≃ Fin 1 ⊕ (I ⊕ Unit) :=
  finSumFinEquiv.symm.trans ((idx.sumCongr (Equiv.refl (Fin 1))).trans unaryLabelShuffle)

theorem unaryPostIndex_active (idx : Fin m ≃ Fin 1 ⊕ I) :
    (unaryPostIndex idx).symm (.inl 0) = blowupExtraIndex (finSumFinEquiv.symm : Fin (m+1) ≃ Fin m ⊕ Fin 1) := rfl

variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem unaryPostIndex_retained (idx : Fin m ≃ Fin 1 ⊕ I) (w : Fin (m+1) → RV0 O) :
    retainedUnaryLabel O (w ∘ (unaryPostIndex idx).symm) ∘ idx =
      w ∘ blowupOldIndices (finSumFinEquiv.symm : Fin (m+1) ≃ Fin m ⊕ Fin 1) := by
  funext j
  change retainedUnaryLabel O (w ∘ (unaryPostIndex idx).symm) (idx j) = w (finSumFinEquiv (.inl j))
  generalize eq : idx j = i
  cases i with
  | inl i =>
    rw [Subsingleton.elim i (0 : Fin 1)] at eq ⊢
    change w (finSumFinEquiv (.inl (idx.symm (.inl 0)))) = w (finSumFinEquiv (.inl j))
    rw [← eq,idx.symm_apply_apply]
  | inr i =>
    change w (finSumFinEquiv (.inl (idx.symm (.inr i)))) = w (finSumFinEquiv (.inl j))
    rw [← eq,idx.symm_apply_apply]

theorem reindexed_unary_post_labels (A : Set (K × (I → RV0 O))) (idx : Fin m ≃ Fin 1 ⊕ I)
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (full : IsUnaryPullback O A) (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t)
    (w : Fin (m+1) → RV0 O) :
    let idx' : Fin (m+1) ≃ Fin m ⊕ Fin 1 := finSumFinEquiv.symm
    let t := w ∘ blowupOldIndices idx'
    let a := t (idx.symm (.inl 0))
    let b := w (blowupExtraIndex idx')
    w ∈ reindexedUnaryLabels O (encodedUnaryImage O A T) (unaryPostIndex idx) ↔
      t ∈ reindexedUnaryLabels O A idx ∧
      ((t ∘ idx.symm ∈ translatedUnaryCut O T ∧ unsignedValue O b < unsignedValue O a) ∨
        (t ∘ idx.symm ∉ translatedUnaryCut O T ∧ b = a)) := by
  intro idx' t a b
  let w' := w ∘ (unaryPostIndex idx).symm
  have retained : retainedUnaryLabel O w' = t ∘ idx.symm := by
    funext i
    have eq := congrFun (unaryPostIndex_retained O idx w) (idx.symm i)
    change retainedUnaryLabel O w' (idx (idx.symm i)) = t (idx.symm i) at eq
    rwa [idx.apply_symm_apply] at eq
  have h := encoded_translation_labels_by_offset O A T full valid w'
  dsimp only at h
  rw [retained] at h
  exact h

end GeneralizedEuler.Section5
