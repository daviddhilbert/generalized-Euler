module

public import Section5.UnaryTranslationLabels
public import Section5.DefinableUnaryGrading
public import Section5.DefinableUnaryOffsetFiniteness

/-! Read the post-translation label using the finite RV index set.
The old active term remains available as the appended coordinate. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

variable {K : Type*} [Field K] (O : ValuationSubring K) {I : Type}

theorem unaryLabelSet_iff_decoded {A : Set (K × (I → RV0 O))} (t : Fin 1 ⊕ I → RV0 O) :
    t ∈ unaryLabelSet O A ↔ decodeUnaryLabel O t ∈ unaryMixedLabel O '' A := by
  constructor
  · rintro ⟨a,ha,eq⟩
    exact ⟨unaryPair O a,ha,congrArg (decodeUnaryLabel O) eq⟩
  · rintro ⟨x,hx,eq⟩
    let a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I)
      | .vf => fun _ => x.1
      | .rv => x.2
    refine ⟨a,hx,?_⟩
    funext i
    cases i with
    | inl i =>
      rw [Subsingleton.elim i (0 : Fin 1)]
      exact congrArg Prod.fst eq
    | inr i => exact congrFun (congrArg Prod.snd eq) i

@[expose] def retainedUnaryLabel (w : Fin 1 ⊕ (I ⊕ Unit) → RV0 O) : Fin 1 ⊕ I → RV0 O :=
  Sum.elim (fun _ => w (.inr (.inr ()))) (fun i => w (.inr (.inl i)))

theorem encoded_unary_translation_labels (A : Set (K × (I → RV0 O)))
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (full : IsUnaryPullback O A) (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t)
    (w : Fin 1 ⊕ (I ⊕ Unit) → RV0 O) :
    let t := retainedUnaryLabel O w
    let r := t ∘ Sum.inr
    let a := t (.inl 0)
    let b := w (.inl 0)
    w ∈ unaryLabelSet O (encodedUnaryImage O A T) ↔ t ∈ unaryLabelSet O A ∧
      (((r,a) ∈ T.locus ∧ a ≠ 0 ∧ unsignedValue O b < unsignedValue O a) ∨
        (((r,a) ∉ T.locus ∨ a = 0) ∧ b = a)) := by
  intro t r a b
  rw [unaryLabelSet_iff_decoded O w,unaryLabelSet_iff_decoded O t]
  have transfer : decodeUnaryLabel O w ∈ unaryMixedLabel O '' encodedUnaryImage O A T ↔
      (b,(r,a)) ∈ unaryMixedLabel O '' (recodeUnaryTranslation O T '' A) := by
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,h⟩
      refine ⟨x,hx,?_⟩
      exact congrArg (fun v : RV0 O × (I ⊕ Unit → RV0 O) => (v.1,(unaryTagAppend O).symm v.2)) h
    · rintro ⟨x,hx,h⟩
      refine ⟨reindexUnaryPoint (unaryTagAppend O) x,⟨x,hx,rfl⟩,?_⟩
      have tag : unaryTagAppend O (I := I) (r,a) = w ∘ Sum.inr :=
        (unaryTagAppend O).apply_symm_apply (w ∘ Sum.inr)
      exact (congrArg (fun v : RV0 O × ((I → RV0 O) × RV0 O) => (v.1,unaryTagAppend O v.2)) h).trans
        (Prod.ext rfl tag)
  rw [transfer,unary_translation_labels O A T full valid]
  rfl

theorem unary_offset_ne_zero_iff (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t) (r : I → RV0 O) (t : RV0 O) :
    T.offset r t ≠ 0 ↔ (r,t) ∈ T.locus ∧ t ≠ 0 := by
  classical
  have eq : T.offset r t = if (r,t) ∈ T.locus then T.focus r t else 0 := rfl
  by_cases h : (r,t) ∈ T.locus
  · rw [eq,ite_eq_left h]
    exact ⟨fun nz => ⟨h,fun ht => nz ((rv_eq_zero_iff O).1 ((valid r t h).trans ht))⟩,
      fun ⟨_,nz⟩ hz => nz ((valid r t h).symm.trans ((rv_eq_zero_iff O).2 hz))⟩
  · rw [eq,ite_eq_right h]
    exact iff_of_false (fun h => h rfl) (fun h' => h h'.1)

@[expose] def translatedUnaryCut (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O))) :
    Set ((Fin 1 ⊕ I) → RV0 O) :=
  {w | T.offset (w ∘ Sum.inr) (w (.inl 0)) ≠ 0}

theorem encoded_translation_labels_by_offset (A : Set (K × (I → RV0 O)))
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (full : IsUnaryPullback O A) (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t)
    (w : Fin 1 ⊕ (I ⊕ Unit) → RV0 O) :
    let t := retainedUnaryLabel O w
    w ∈ unaryLabelSet O (encodedUnaryImage O A T) ↔ t ∈ unaryLabelSet O A ∧
      ((t ∈ translatedUnaryCut O T ∧ unsignedValue O (w (.inl 0)) < unsignedValue O (t (.inl 0))) ∨
        (t ∉ translatedUnaryCut O T ∧ w (.inl 0) = t (.inl 0))) := by
  classical
  intro t
  have h := encoded_unary_translation_labels O A T full valid w
  refine h.trans ?_
  let r := t ∘ Sum.inr
  let a := t (.inl 0)
  let b := w (.inl 0)
  change (_ ∧ (((r,a) ∈ T.locus ∧ a ≠ 0 ∧ unsignedValue O b < unsignedValue O a) ∨
      (((r,a) ∉ T.locus ∨ a = 0) ∧ b = a))) ↔
    (_ ∧ ((T.offset r a ≠ 0 ∧ unsignedValue O b < unsignedValue O a) ∨ (¬ T.offset r a ≠ 0 ∧ b = a)))
  rw [unary_offset_ne_zero_iff O T valid]
  simp only [not_and_or,not_not,and_assoc,t]

variable [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
  {E : Type*} [L.Structure (Residue O)] (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) [Finite I]

theorem translatedUnaryCut_definable (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (defT : UnaryOffsetDefinable O hO power S T) :
    isRVSet (canonicalStructure (L := L) O hO power) S (translatedUnaryCut O T) := by
  have graph := unary_offset_label_graph O hO power S T defT
  have h := graph.preimage ((field_eq_zero_definable O hO power S (V := MixedVariables 1 Empty) 0).compl)
  unfold isRVSet
  convert h using 1
  ext a
  let c := T.offset (a .rv ∘ Sum.inr) (a .rv (.inl 0))
  change c ≠ 0 ↔ ∃ v : fieldAssignment 1 (CanonicalSort O), v .vf 0 ≠ 0 ∧ v .vf 0 = c
  exact ⟨fun hc => ⟨fieldTupleAssignment (fun _ => c),hc,rfl⟩,fun ⟨_,hv,eq⟩ => eq ▸ hv⟩

end GeneralizedEuler.Section5
