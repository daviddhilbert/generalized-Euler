module

public import Section5.LiftSpecialTail

/-! A chain can be replayed with extra untouched RV coordinates. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] {O : ValuationSubring K} {n : ℕ}
  {I J H : Type}

@[expose] def forgetExtraTags (p : PreparationPoint O (Fin n) (I ⊕ H)) :
    PreparationPoint O (Fin n) I :=
  (p.1, p.2 ∘ Sum.inl)

@[expose] def CoordinatePreparation.keepTags (C : CoordinatePreparation O (Fin n) I) :
    CoordinatePreparation O (Fin n) (I ⊕ H) where
  coord := C.coord
  translation := {
    locus := {p | ((p.1.1, p.1.2 ∘ Sum.inl), p.2) ∈ C.translation.locus}
    focus := fun p => C.translation.focus (p.1, p.2 ∘ Sum.inl) }

theorem forgetExtraTags_label_eq (a b : PreparationPoint O (Fin n) (I ⊕ H))
    (h : preparationLabel a = preparationLabel b) :
    preparationLabel (forgetExtraTags a) = preparationLabel (forgetExtraTags b) := by
  obtain ⟨hf,hr⟩ := Prod.mk.inj h
  exact Prod.ext hf (congrArg (fun t => t ∘ Sum.inl) hr)

theorem CoordinatePreparation.keepTags_valid (C : CoordinatePreparation O (Fin n) I)
    (A : Set (PreparationPoint O (Fin n) I)) (hA : C.ValidOn O A) :
    (C.keepTags (H := H)).ValidOn O (forgetExtraTags ⁻¹' A) := by
  intro p hp hl
  have ha : forgetExtraTags p ∈ preparationHull O A := by
    obtain ⟨z,hz,he⟩ := hp
    exact ⟨forgetExtraTags z,hz,forgetExtraTags_label_eq z p he⟩
  exact hA _ ha hl

/-- Pack the auxiliary tag appended by a lifted translation alongside
the original ones. Its old-tag projection is a permutation. -/
def permuteAppendedTag : Option I ⊕ H → Option (I ⊕ H)
  | .inl i => i.map Sum.inl
  | .inr h => some (.inr h)

theorem permuteAppendedTag_surjective :
    Function.Surjective (permuteAppendedTag (I := I) (H := H)) := by
  rintro (_ | i)
  · exact ⟨.inl none,rfl⟩
  · cases i with
    | inl i => exact ⟨.inl (some i),rfl⟩
    | inr h => exact ⟨.inr h,rfl⟩

theorem CoordinatePreparation.keepTags_map (C : CoordinatePreparation O (Fin n) I)
    (p : PreparationPoint O (Fin n) (I ⊕ H)) :
    regularizeBy O (Sum.inr ∘ permuteAppendedTag) (C.keepTags.map p) =
      mapKeepingTags (H := H) C.map p := by
  refine Prod.ext ?_ ?_
  · change (C.keepTags.map p).1 = (C.map (forgetExtraTags p)).1
    rfl
  · funext j
    rcases j with (⟨⟩ | i) | h <;> rfl

theorem image_mapKeepingTags
    (f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) J)
    (A : Set (PreparationPoint O (Fin n) I)) :
    mapKeepingTags (H := H) f '' (forgetExtraTags ⁻¹' A) =
      forgetExtraTags ⁻¹' (f '' A) := by
  ext p
  constructor
  · rintro ⟨q,hq,he⟩
    exact ⟨forgetExtraTags q,hq,(congrArg forgetExtraTags he)⟩
  · rintro ⟨q,hq,he⟩
    let r : PreparationPoint O (Fin n) (I ⊕ H) :=
      (q.1, Sum.elim q.2 (p.2 ∘ Sum.inr))
    refine ⟨r,hq,?_⟩
    change ((f q).1, Sum.elim (f q).2 (p.2 ∘ Sum.inr)) = p
    rw [he]
    refine Prod.ext ?_ ?_
    · rfl
    · funext i; cases i <;> rfl

/-- A special chain extends while fixing any additional RV tuple. -/
theorem SpecialChain.keepTags {A : Set (PreparationPoint O (Fin n) I)}
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) J}
    (h : SpecialChain O (Fin n) A f) :
    SpecialChain O (Fin n) (forgetExtraTags ⁻¹' A) (mapKeepingTags (H := H) f) := by
  induction h with
  | id A =>
    refine SpecialChain.congr (.id _) ?_
    intro p _
    refine Prod.ext ?_ ?_
    · rfl
    · funext i; cases i <;> rfl
  | @translation I' A C hC =>
    let pick : Option I' ⊕ H → Fin n ⊕ Option (I' ⊕ H) :=
      Sum.inr ∘ permuteAppendedTag
    have recover a (_ : a ∈ C.keepTags.map '' (forgetExtraTags ⁻¹' A))
        b (_ : b ∈ C.keepTags.map '' (forgetExtraTags ⁻¹' A))
        (he : preparationLabel (regularizeBy O pick a) = preparationLabel (regularizeBy O pick b)) :
        a.2 = b.2 := by
      have htags := congrArg Prod.snd he
      funext i
      obtain ⟨j,rfl⟩ := permuteAppendedTag_surjective i
      exact congrFun htags j
    refine SpecialChain.congr (.append
      (.translation _ C.keepTags (C.keepTags_valid A hC)) (.regularization _ pick recover)) ?_
    exact fun p _ => C.keepTags_map p
  | @regularization I' J' A source recover =>
    let pick : J' ⊕ H → Fin n ⊕ (I' ⊕ H) :=
      Sum.elim (Sum.map _root_.id Sum.inl ∘ source) (Sum.inr ∘ Sum.inr)
    have eq (p) : regularizeBy O pick p = mapKeepingTags (H := H) (regularizeBy O source) p := by
      refine Prod.ext ?_ ?_
      · rfl
      · funext i
        cases i with
        | inl i =>
          change Sum.elim (rv O ∘ p.1) p.2 (Sum.map _root_.id Sum.inl (source i)) =
            Sum.elim (rv O ∘ p.1) (p.2 ∘ Sum.inl) (source i)
          cases source i <;> rfl
        | inr i => rfl
    have hrec a (ha : a ∈ forgetExtraTags ⁻¹' A) b (hb : b ∈ forgetExtraTags ⁻¹' A)
        (he : preparationLabel (regularizeBy O pick a) = preparationLabel (regularizeBy O pick b)) :
        a.2 = b.2 := by
      rw [eq,eq] at he
      have ht := forgetExtraTags_label_eq _ _ he
      have h₁ := recover (forgetExtraTags a) ha (forgetExtraTags b) hb ht
      have h₂ := congrArg Prod.snd he
      funext i
      cases i with
      | inl i => exact congrFun h₁ i
      | inr j => exact congrFun h₂ (.inr j)
    exact SpecialChain.congr (.regularization _ pick hrec) (fun p _ => eq p)
  | @append _ _ _ A f _ hf hg ihf ihg =>
    have he := image_mapKeepingTags (H := H) f A
    refine SpecialChain.congr (.append ihf (he.symm ▸ ihg)) ?_
    exact fun p _ => rfl
  | congr hf he ih =>
    refine ih.congr ?_
    intro p hp
    exact congrArg (fun a => (a.1, Sum.elim a.2 (p.2 ∘ Sum.inr))) (he hp)

end GeneralizedEuler.Section5
