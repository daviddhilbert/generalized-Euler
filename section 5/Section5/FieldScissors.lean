module

public import Section5.DefinableRelations
public import Section4.Scissors

/-! Positive VF classes from mixed definable sets with finite field
fibers. The morphisms may change the ambient arities. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  (M : SortedStructure L E X) (S : SortedSubstructure M)

/-- The graph of a mixed bijection is definable over the common
two-sorted base. -/
@[expose] def MixedDefinablyEquivalent {V W : TCsort → Type}
    (A : Set (SortedAssignment X V)) (B : Set (SortedAssignment X W)) : Prop :=
  ∃ e : A ≃ B, DefinableRelation M S.carrier
    (fun a b => ∃ ha : a ∈ A, (e ⟨a,ha⟩).val = b)

namespace MixedDefinablyEquivalent

variable {M S}

theorem refl {V : TCsort → Type} [Finite (V .vf)] [Finite (V .rv)]
    {A : Set (SortedAssignment X V)} (defA : SortedDefinableOver M S.carrier A) :
    MixedDefinablyEquivalent M S A A := by
  refine ⟨Equiv.refl A,?_⟩
  apply (DefinableRelation.diagonal.inter_left defA).congr
  intro a b
  exact ⟨fun ⟨h,ha⟩ => ⟨ha,h⟩,fun ⟨ha,h⟩ => ⟨h,ha⟩⟩

theorem symm {V W : TCsort → Type}
    {A : Set (SortedAssignment X V)} {B : Set (SortedAssignment X W)}
    (h : MixedDefinablyEquivalent M S A B) : MixedDefinablyEquivalent M S B A := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,he.transpose.congr ?_⟩
  intro b a
  constructor
  · rintro ⟨ha,eq⟩
    have hb : b ∈ B := eq ▸ (e ⟨a,ha⟩).property
    have hEq : e ⟨a,ha⟩ = ⟨b,hb⟩ := Subtype.ext eq
    refine ⟨hb,?_⟩
    exact congrArg Subtype.val (e.symm_apply_eq.2 hEq.symm)
  · rintro ⟨hb,eq⟩
    have ha : a ∈ A := eq ▸ (e.symm ⟨b,hb⟩).property
    have hEq : e.symm ⟨b,hb⟩ = ⟨a,ha⟩ := Subtype.ext eq
    exact ⟨ha,congrArg Subtype.val (e.symm_apply_eq.1 hEq).symm⟩

theorem trans {V W Y : TCsort → Type} [Finite (W .vf)] [Finite (W .rv)]
    {A : Set (SortedAssignment X V)} {B : Set (SortedAssignment X W)}
    {C : Set (SortedAssignment X Y)}
    (h : MixedDefinablyEquivalent M S A B) (g : MixedDefinablyEquivalent M S B C) :
    MixedDefinablyEquivalent M S A C := by
  obtain ⟨e,he⟩ := h
  obtain ⟨f,hf⟩ := g
  refine ⟨e.trans f,(he.comp hf).congr ?_⟩
  intro a c
  constructor
  · rintro ⟨b,⟨ha,eab⟩,hb,ebc⟩
    have eq : e ⟨a,ha⟩ = ⟨b,hb⟩ := Subtype.ext eab
    refine ⟨ha,?_⟩
    change (f (e ⟨a,ha⟩)).val = c
    rw [eq]
    exact ebc
  · rintro ⟨ha,eq⟩
    exact ⟨(e ⟨a,ha⟩).val,⟨ha,rfl⟩,(e ⟨a,ha⟩).property,eq⟩

/-- Restrict a definable bijection to a definable portion of its target. -/
theorem restrict_target {V W : TCsort → Type} [Finite (W .vf)] [Finite (W .rv)]
    {A : Set (SortedAssignment X V)} {B : Set (SortedAssignment X W)}
    (e : A ≃ B)
    (graph : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ A, (e ⟨a,ha⟩).val = b))
    (C : Set (SortedAssignment X W)) (sub : C ⊆ B) (defC : SortedDefinableOver M S.carrier C) :
    let D := {a | ∃ h : a ∈ A, (e ⟨a,h⟩).val ∈ C}
    SortedDefinableOver M S.carrier D ∧ MixedDefinablyEquivalent M S D C := by
  intro D
  have hD : SortedDefinableOver M S.carrier D := by
    convert graph.preimage defC using 1
    ext a
    constructor
    · rintro ⟨ha,hc⟩
      exact ⟨_,hc,ha,rfl⟩
    · rintro ⟨c,hc,ha,he⟩
      exact ⟨ha,he.symm ▸ hc⟩
  let f (a : D) : C := ⟨(e ⟨a.val,a.property.choose⟩).val,a.property.choose_spec⟩
  have bij : Function.Bijective f := by
    constructor
    · intro x y he
      have eq := e.injective (Subtype.ext (congrArg (fun c : C => c.val) he))
      exact Subtype.ext (congrArg (fun a : A => a.val) eq)
    · intro y
      let a := e.symm ⟨y.val,sub y.property⟩
      have eq : (e a).val = y.val := congrArg Subtype.val (e.apply_symm_apply _)
      have mem : a.val ∈ D := ⟨a.property,eq.symm ▸ y.property⟩
      exact ⟨⟨a.val,mem⟩,Subtype.ext eq⟩
  refine ⟨hD,Equiv.ofBijective f bij,(graph.inter_left hD).congr ?_⟩
  intro a b
  constructor
  · rintro ⟨⟨_,he⟩,ha⟩
    exact ⟨ha,he⟩
  · rintro ⟨ha,he⟩
    exact ⟨⟨ha.choose,he⟩,ha⟩

end MixedDefinablyEquivalent

section Objects

variable [TopologicalSpace (X .vf)]

abbrev VFObject := Σ k, FieldObject M S k

abbrev VFVars (A : VFObject M S) := MixedVariables A.2.vfArity (Fin A.2.rvArity)

@[expose] def mixedProduct {V W : TCsort → Type}
    (A : Set (SortedAssignment X V)) (B : Set (SortedAssignment X W)) :
    Set (SortedAssignment X (SumVariables V W)) :=
  {a | (fun s => a s ∘ Sum.inl) ∈ A ∧ (fun s => a s ∘ Sum.inr) ∈ B}

abbrev VFExpression := MvPolynomial (VFObject M S) ℕ

/-- The filtration bound is carried by the objects. The relations
record definable isomorphisms, cuts, and products of their carriers. -/
inductive VFRelation : VFExpression M S → VFExpression M S → Prop where
  | iso (A B : VFObject M S) (h : MixedDefinablyEquivalent M S A.2.carrier B.2.carrier) :
    VFRelation (MvPolynomial.X A) (MvPolynomial.X B)
  | zero (A : VFObject M S) (h : A.2.carrier = ∅) :
    VFRelation (MvPolynomial.X A) 0
  | one (A : VFObject M S) (h : ∃ a, A.2.carrier = {a}) :
    VFRelation (MvPolynomial.X A) 1
  | cut (A B C : VFObject M S) (D E : Set (SortedAssignment X (VFVars M S A)))
      (hd : SortedDefinableOver M S.carrier D) (he : SortedDefinableOver M S.carrier E)
      (disj : Disjoint D E) (cover : D ∪ E = A.2.carrier)
      (iB : MixedDefinablyEquivalent M S D B.2.carrier)
      (iC : MixedDefinablyEquivalent M S E C.2.carrier) :
    VFRelation (MvPolynomial.X A) (MvPolynomial.X B + MvPolynomial.X C)
  | product (A B C : VFObject M S)
      (e : MixedDefinablyEquivalent M S (mixedProduct A.2.carrier B.2.carrier) C.2.carrier) :
    VFRelation (MvPolynomial.X C) (MvPolynomial.X A * MvPolynomial.X B)

abbrev VFSemiring := (ringConGen (VFRelation M S)).Quotient

@[expose] def fieldClass (A : VFObject M S) : VFSemiring M S :=
  (ringConGen (VFRelation M S)).mk' (MvPolynomial.X A)

theorem field_scissors_sound {a b} (h : VFRelation M S a b) :
    (ringConGen (VFRelation M S)).mk' a = (ringConGen (VFRelation M S)).mk' b :=
  Quotient.sound (RingConGen.Rel.of _ _ h)

theorem fieldClass_of_iso {A B : VFObject M S}
    (h : MixedDefinablyEquivalent M S A.2.carrier B.2.carrier) :
    fieldClass M S A = fieldClass M S B :=
  field_scissors_sound M S (.iso A B h)

end Objects

end GeneralizedEuler.Section5
