module

public import Section5.FocusTranslationImage
public import Section5.ObjectLiftRestrictions
public import Section5.ElementaryClassSteps

/-! A focus on a proper definable RV locus leaves its complement as
an untouched summand of the elementary blowup. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1)) (j : Fin (k+1))
  (D : Set (Fin U.arity → RV0 O))

@[expose] def partialFocusBase (x : RetainedFocusTuple (L := L) O hO power S U) :
    (Fin k → RV0 O) × U.carrier := (rv O ∘ x.1,x.2)

@[expose] def partialFocusTranslation (c : (Fin k → K) → U.carrier → K) :
    RelativeTranslation O (partialFocusBase O hO power S U) :=
  ⟨{t | t.1.2.val ∈ D},fun x _ => c x.1 x.2⟩

theorem partial_focus_translation_image
    (c : (Fin k → K) → U.carrier → K)
    (valid : ∀ (x : Fin k → K) (u : U.carrier), u.val ∈ D →
      U.label u ∘ j.succAbove = rv O ∘ x → rv O (c x u) = U.label u j) :
    (partialFocusTranslation O hO power S U D c).map '' focusTranslationSource O hO power S U j =
      {y | y.1.2.val ∈ D ∧ y ∈ focusTranslationTarget O hO power S U j} ∪
      {y | y.1.2.val ∉ D ∧
        U.label y.1.2 ∘ j.succAbove = rv O ∘ y.1.1 ∧
        y.2.2 = U.label y.1.2 j ∧ rv O y.2.1 = y.2.2} := by
  let T := partialFocusTranslation O hO power S U D c
  let A : Set (((Fin k → RV0 O) × U.carrier) × RV0 O) :=
    {t | U.label t.1.2 ∘ j.succAbove = t.1.1 ∧ t.2 = U.label t.1.2 j}
  have h := T.image_pullback A (by
    intro x t hs hd
    have ht : t = U.label x.2 j := hs.2
    exact ⟨ht.symm ▸ U.nonzero x.2 j,(valid x.1 x.2 hd hs.1).trans ht.symm⟩)
  change T.map '' focusTranslationSource O hO power S U j = _ at h
  rw [h]
  ext y
  change (_ ∧ _) ∧ ((_ ∧ _) ∨ (_ ∧ _)) ↔ (_ ∧ _ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _)
  constructor
  · rintro ⟨⟨hr,ht⟩,⟨hd,hv⟩ | ⟨hd,hv⟩⟩
    · exact Or.inl ⟨hd,hr,ht,hv⟩
    · exact Or.inr ⟨hd,hr,ht,hv⟩
  · rintro (⟨hd,hr,ht,hv⟩ | ⟨hd,hr,ht,hv⟩)
    · exact ⟨⟨hr,ht⟩,Or.inl ⟨hd,hv⟩⟩
    · exact ⟨⟨hr,ht⟩,Or.inr ⟨hd,hv⟩⟩

theorem partial_focus_blowup_class (hneg : rv O (-1) ∈ S.carrier .rv)
    (hd : isRVSet 𝓜 S D) (sub : D ⊆ U.carrier) :
    let V := ObjectLift.restrictTags U sub hd
    let W := ObjectLift.restrictTags U (Set.sdiff_subset : U.carrier \ D ⊆ U.carrier)
      (U.definable.inter hd.compl)
    ∀ hdel : ∀ t : Fin k → RV0 O, {a ∈ Set.range V.label | a ∘ j.succAbove = t}.Finite,
    let idx : Fin (V.arity+1) ≃ Fin V.arity ⊕ Fin 1 := finSumFinEquiv.symm
    ElementaryClassStep O hO power S hneg (objectClass 𝓜 S ⟨k+1,U⟩)
      (objectClass 𝓜 S ⟨k,zeroBlowupObject V j hdel⟩ +
        objectClass 𝓜 S ⟨k+1,translatedPositiveObject O hO power S V idx j hneg hdel⟩ +
        objectClass 𝓜 S ⟨k+1,W⟩) := by
  classical
  intro V W hdel idx
  have cut : objectClass 𝓜 S ⟨_,U⟩ = objectClass 𝓜 S ⟨_,V⟩ + objectClass 𝓜 S ⟨_,W⟩ := by
    apply scissors_sound 𝓜 S
    have disj : Disjoint D (U.carrier \ D) := Set.disjoint_left.2 fun _ hx hy => hy.2 hx
    have cover : D ∪ (U.carrier \ D) = U.carrier := Set.union_sdiff_cancel sub
    exact RVRelation.cut U V W D (U.carrier \ D) hd (U.definable.inter hd.compl) disj cover
      ⟨Equiv.refl _,definable_identity_label 𝓜 S hd⟩
      ⟨Equiv.refl _,definable_identity_label 𝓜 S (U.definable.inter hd.compl)⟩
  let Z := zeroBlowupObject V j hdel
  refine Or.inr ⟨⟨k,Z⟩,objectClass 𝓜 S ⟨k+1,W⟩,?_,?_⟩
  · rw [cut,blowup_original_class_factor O hO power S V j hdel]
    rfl
  · rw [translatedPositiveObject_class O hO power S V idx j hneg hdel,
      positiveBlowup_class_factor O hO power S V idx hneg j hdel,mul_add,mul_one]
    rfl

end GeneralizedEuler.Section5
