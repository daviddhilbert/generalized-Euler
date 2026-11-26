module

public import Section5.MixedGraphIsomorphisms

/-! An isomorphism of finite tagged mixed families is a bijection
with a fixed-base definable graph for each source and target tag. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  (M : SortedStructure L E X) (S : SortedSubstructure M)

structure MixedTaggedFamily where
  Tag : Type
  [finiteTag : Finite Tag]
  coordinates : Tag → TCsort → Type
  [finiteCoordinates : ∀ i s, Finite (coordinates i s)]
  piece : (i : Tag) → Set (SortedAssignment X (coordinates i))
  definable : ∀ i, SortedDefinableOver M S.carrier (piece i)

namespace MixedTaggedFamily

attribute [instance] finiteTag finiteCoordinates

variable {M S} (A B C : MixedTaggedFamily M S)

abbrev Points := (i : A.Tag) × A.piece i

@[expose] def graphOver (f : A.Points → B.Points) (i : A.Tag) (j : B.Tag)
    (x : SortedAssignment X (A.coordinates i)) (y : SortedAssignment X (B.coordinates j)) : Prop :=
  ∃ (hx : x ∈ A.piece i) (hy : y ∈ B.piece j), f ⟨i,⟨x,hx⟩⟩ = ⟨j,⟨y,hy⟩⟩

@[expose] def HasDefinableGraph (f : A.Points → B.Points) : Prop :=
  ∀ i j, DefinableRelation M S.carrier (graphOver A B f i j)

@[expose] def Iso : Prop := ∃ f : A.Points ≃ B.Points, A.HasDefinableGraph B f

theorem iso_retag (t : A.Tag ≃ B.Tag)
    (components : ∀ i, MixedDefinablyEquivalent M S (A.piece i) (B.piece (t i))) : A.Iso B := by
  classical
  choose f hf using components
  let e : A.Points ≃ B.Points := Equiv.sigmaCongr t f
  refine ⟨e,fun i j => ?_⟩
  by_cases h : t i = j
  · subst j
    apply (hf i).congr
    intro x y
    constructor
    · rintro ⟨hx,rfl⟩
      exact ⟨hx,(f i ⟨x,hx⟩).property,rfl⟩
    · rintro ⟨hx,hy,eq⟩
      change (⟨t i,f i ⟨x,hx⟩⟩ : B.Points) = ⟨t i,⟨y,hy⟩⟩ at eq
      have same : f i ⟨x,hx⟩ = ⟨y,hy⟩ := eq_of_heq (Sigma.mk.inj_iff.mp eq).2
      exact ⟨hx,congrArg Subtype.val same⟩
  · unfold DefinableRelation
    refine ⟨.falsum,fun a => ⟨?_,False.elim⟩⟩
    rintro ⟨_,_,eq⟩
    exact h (congrArg Sigma.fst eq)

theorem iso_refl : A.Iso A :=
  A.iso_retag A (Equiv.refl _) (fun i => .refl (A.definable i))

theorem iso_symm (h : A.Iso B) : B.Iso A := by
  obtain ⟨f,defF⟩ := h
  refine ⟨f.symm,fun j i => (defF i j).transpose.congr ?_⟩
  intro y x
  exact ⟨fun ⟨hx,hy,e⟩ => ⟨hy,hx,f.symm_apply_eq.2 e.symm⟩,
    fun ⟨hy,hx,e⟩ => ⟨hx,hy,(f.symm_apply_eq.1 e).symm⟩⟩

theorem iso_trans (ab : A.Iso B) (bc : B.Iso C) : A.Iso C := by
  obtain ⟨f,defF⟩ := ab
  obtain ⟨g,defG⟩ := bc
  refine ⟨f.trans g,fun i k => ?_⟩
  let R (j : B.Tag) (x : SortedAssignment X (A.coordinates i)) (z : SortedAssignment X (C.coordinates k)) :=
    ∃ y, A.graphOver B f i j x y ∧ B.graphOver C g j k y z
  have d : DefinableRelation M S.carrier (fun x z => ∃ j, R j x z) := by
    unfold DefinableRelation
    convert SortedDefinableOver.iUnion (fun j => (defF i j).comp (defG j k)) using 1
    ext w
    rw [Set.mem_iUnion]
    rfl
  apply d.congr
  intro x z
  constructor
  · rintro ⟨j,y,⟨hx,hy,e⟩,hy',hz,t⟩
    exact ⟨hx,hz,(congrArg g e).trans t⟩
  · rintro ⟨hx,hz,h⟩
    let y := f ⟨i,⟨x,hx⟩⟩
    exact ⟨y.1,y.2.val,⟨hx,y.2.property,rfl⟩,y.2.property,hz,h⟩

end MixedTaggedFamily

end GeneralizedEuler.Section5
