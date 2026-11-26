module

public import Section5.DefinableContractionIso
public import Section5.DefinablePairedCenterChains
public import Section5.UnaryDegreeContraction
public import Section5.UnaryGradedObjects

/-! Mutual unary contraction gives an actual fixed-base RV isomorphism
which preserves the degree of each unary label. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I J : Type} [Finite I] [Finite J]

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def unaryLabelSet {H : Type} (A : Set (K × (H → RV0 O))) : Set ((Fin 1 ⊕ H) → RV0 O) :=
  (fun a : SortedAssignment (CanonicalSort O) (MixedVariables 1 H) => encodeUnaryLabel O (unaryPair O a)) ''
    {a | unaryPair O a ∈ A}

theorem unaryLabelSet_definable {H : Type} [Finite H] {A : Set (K × (H → RV0 O))}
    (defA : UnaryPullbackDefinable O hO power S A) : isRVSet 𝓜 S (unaryLabelSet O A) := by
  have graph := (unaryLabelAssignment_definable O hO power S (H := H)).image defA
  unfold isRVSet
  convert graph using 1
  ext t
  change (∃ a, unaryPair O a ∈ A ∧ encodeUnaryLabel O (unaryPair O a) = t .rv) ↔
    ∃ a, unaryPair O a ∈ A ∧ unaryLabelAssignment O a = t
  constructor
  · rintro ⟨a,ha,eq⟩
    refine ⟨a,ha,?_⟩
    funext s i
    cases s
    · exact i.elim
    · exact congrFun eq i
  · rintro ⟨a,ha,eq⟩
    exact ⟨a,ha,congrFun eq .rv⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[expose] def unaryAssignmentEquiv {H : Type} (A : Set (K × (H → RV0 O))) :
    {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 H) | unaryPair O a ∈ A} ≃ A where
  toFun a := ⟨unaryPair O a.val,a.property⟩
  invFun x := ⟨(fun | .vf => fun _ => x.val.1 | .rv => x.val.2),x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext s i
    cases s
    · rw [Subsingleton.elim i (0 : Fin 1)]
    · rfl
  right_inv _ := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem encode_unary_label_eq {H : Type} (x y : K × (H → RV0 O)) :
    encodeUnaryLabel O x = encodeUnaryLabel O y ↔ unaryMixedLabel O x = unaryMixedLabel O y := by
  constructor
  · intro h
    exact congrArg (decodeUnaryLabel O) h
  · intro h
    funext i
    cases i with
    | inl i => exact congrArg Prod.fst h
    | inr i => exact congrFun (congrArg Prod.snd h) i

theorem mutually_contracted_unary_labels {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
    (e : A ≃ B) (defE : UnaryMixedGraphDefinable O hO power S e)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e)
    (backward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e.symm)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) :
    ∃ f : unaryLabelSet O A ≃ unaryLabelSet O B,
      SortedDefinableOver 𝓜 S.carrier (rvGraph fun x => (f x).val) ∧
      ∀ x, x.val (.inl 0) = 0 ↔ (f x).val (.inl 0) = 0 := by
  let aIso := unaryAssignmentEquiv O A
  let bIso := unaryAssignmentEquiv O B
  let e' := aIso.trans (e.trans bIso.symm)
  let p {H : Type} (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 H)) := encodeUnaryLabel O (unaryPair O a)
  have dp {H : Type} [Finite H] : DefinableRelation 𝓜 S.carrier
      (fun a (b : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1 ⊕ H))) => p a = b .rv) := by
    refine (unaryLabelAssignment_definable O hO power S (H := H)).congr ?_
    intro a b
    constructor
    · intro h
      exact congrFun h .rv
    · intro h
      funext s i
      cases s
      · exact i.elim
      · exact congrFun h i
  have graph : DefinableRelation 𝓜 S.carrier (fun a b => ∃ h : unaryPair O a ∈ A, (e' ⟨a,h⟩).val = b) := by
    refine defE.congr ?_
    intro a b
    constructor
    · rintro ⟨ha,eq⟩
      refine ⟨ha,?_⟩
      funext s i
      cases s
      · rw [Subsingleton.elim i (0 : Fin 1)]
        exact congrArg Prod.fst eq
      · exact congrFun (congrArg Prod.snd eq) i
    · rintro ⟨ha,eq⟩
      exact ⟨ha,congrArg (unaryPair O) eq⟩
  have hf : Contractible (p ∘ Subtype.val) (p ∘ Subtype.val) e' := by
    intro x y eq
    apply (encode_unary_label_eq O _ _).2
    exact forward (aIso x) (aIso y) ((encode_unary_label_eq O _ _).1 eq)
  have hb : Contractible (p ∘ Subtype.val) (p ∘ Subtype.val) e'.symm := by
    intro x y eq
    apply (encode_unary_label_eq O _ _).2
    exact backward (bIso x) (bIso y) ((encode_unary_label_eq O _ _).1 eq)
  obtain ⟨f,hd,eval⟩ := definable_label_iso_of_mutually_contractible e' graph p p (dp (H := I)) (dp (H := J)) hf hb
  refine ⟨f,hd,?_⟩
  intro x
  obtain ⟨a,ha,eq⟩ := x.property
  have hx : (⟨p a,⟨a,ha,rfl⟩⟩ : unaryLabelSet O A) = x := Subtype.ext eq
  have ev : (f ⟨p a,⟨a,ha,rfl⟩⟩).val = p (e' ⟨a,ha⟩).val := eval ⟨a,ha⟩
  have image : (f x).val = p (e' ⟨a,ha⟩).val :=
    (congrArg (fun t : unaryLabelSet O A => (f t).val) hx.symm).trans ev
  have eqA : rv O (a .vf 0) = x.val (.inl 0) := congrFun eq (.inl 0)
  have eqB : (f x).val (.inl 0) = rv O ((e (aIso ⟨a,ha⟩)).val.1) := congrFun image (.inl 0)
  calc
    x.val (.inl 0) = 0 ↔ rv O (a .vf 0) = 0 := ⟨eqA.trans,eqA.symm.trans⟩
    _ ↔ rv O ((e (aIso ⟨a,ha⟩)).val.1) = 0 := by
      simp only [rv_eq_zero_iff]
      exact mutual_unary_contraction_preserves_degree O e fullA fullB forward backward he small (aIso ⟨a,ha⟩)
    _ ↔ (f x).val (.inl 0) = 0 := ⟨eqB.trans,eqB.symm.trans⟩

end GeneralizedEuler.Section5
