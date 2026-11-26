module

public import Section5.FieldScissors
public import Mathlib.Logic.Equiv.Set

/-! Keep the actual bijection with its fixed-base graph when composing,
restricting, or inverting a mixed isomorphism. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {U V W : TCsort → Type}

structure MixedGraphIso (M : SortedStructure L E X) (S : SortedSubstructure M)
    (A : Set (SortedAssignment X U)) (B : Set (SortedAssignment X V)) where
  equiv : A ≃ B
  definable : DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ A, (equiv ⟨a,h⟩).val = b)

namespace MixedGraphIso

variable {A : Set (SortedAssignment X U)} {B : Set (SortedAssignment X V)}
  {C : Set (SortedAssignment X W)}

theorem ext {f g : MixedGraphIso M S A B} (e : ∀ x : A, f.equiv x = g.equiv x) : f = g := by
  cases f
  cases g
  congr
  exact Equiv.ext e

theorem equivalent (f : MixedGraphIso M S A B) : MixedDefinablyEquivalent M S A B :=
  ⟨f.equiv,f.definable⟩

@[expose] def symm (f : MixedGraphIso M S A B) : MixedGraphIso M S B A where
  equiv := f.equiv.symm
  definable := f.definable.transpose.congr (fun b a => by
    constructor
    · rintro ⟨ha,e⟩
      let x : A := ⟨a,ha⟩
      have hb : b ∈ B := e ▸ (f.equiv x).property
      have e' : f.equiv x = ⟨b,hb⟩ := Subtype.ext e
      exact ⟨hb,congrArg Subtype.val (f.equiv.symm_apply_eq.2 e'.symm)⟩
    · rintro ⟨hb,e⟩
      let y : B := ⟨b,hb⟩
      have ha : a ∈ A := e ▸ (f.equiv.symm y).property
      have e' : f.equiv.symm y = ⟨a,ha⟩ := Subtype.ext e
      exact ⟨ha,congrArg Subtype.val ((f.equiv.symm_apply_eq.1 e').symm)⟩)

@[expose] def trans [Finite (V .vf)] [Finite (V .rv)] (f : MixedGraphIso M S A B) (g : MixedGraphIso M S B C) :
    MixedGraphIso M S A C where
  equiv := f.equiv.trans g.equiv
  definable := (f.definable.comp g.definable).congr (fun a c => by
    constructor
    · rintro ⟨b,⟨ha,e⟩,hb,gc⟩
      have eq : f.equiv ⟨a,ha⟩ = ⟨b,hb⟩ := Subtype.ext e
      refine ⟨ha,?_⟩
      change (g.equiv (f.equiv ⟨a,ha⟩)).val = c
      rwa [eq]
    · rintro ⟨ha,eq⟩
      exact ⟨(f.equiv ⟨a,ha⟩).val,⟨ha,rfl⟩,(f.equiv ⟨a,ha⟩).property,eq⟩)

theorem target_definable [Finite (U .vf)] [Finite (U .rv)]
    (f : MixedGraphIso M S A B) (defA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier B := by
  convert f.definable.image defA using 1
  ext b
  constructor
  · intro hb
    let x := f.equiv.symm ⟨b,hb⟩
    exact ⟨x.val,x.property,x.property,congrArg Subtype.val (f.equiv.apply_symm_apply _)⟩
  · rintro ⟨a,_,ha,e⟩
    exact e ▸ (f.equiv ⟨a,ha⟩).property

@[expose] def toRange (f : A → SortedAssignment X V) (inj : Function.Injective f)
    (defF : DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ A, f ⟨a,h⟩ = b)) :
    MixedGraphIso M S A (Set.range f) :=
  ⟨Equiv.ofInjective f inj,defF⟩

@[expose] def rangeOver (f : MixedGraphIso M S A B) {D : Set (SortedAssignment X U)} (sub : D ⊆ A) :
    Set (SortedAssignment X V) :=
  Set.range (fun x : D => (f.equiv ⟨x.val,sub x.property⟩).val)

@[expose] def restrict (f : MixedGraphIso M S A B) {D : Set (SortedAssignment X U)}
    (sub : D ⊆ A) (defD : SortedDefinableOver M S.carrier D) :
    MixedGraphIso M S D (f.rangeOver sub) := by
  apply toRange (fun x : D => (f.equiv ⟨x.val,sub x.property⟩).val)
  · intro x y e
    exact Subtype.ext (congrArg (fun a : A => a.val) (f.equiv.injective (Subtype.ext e)))
  · apply (f.definable.inter_left defD).congr
    intro a b
    exact ⟨fun ⟨⟨_,e⟩,h⟩ => ⟨h,e⟩,fun ⟨h,e⟩ => ⟨⟨sub h,e⟩,h⟩⟩

theorem restrict_apply (f : MixedGraphIso M S A B) {D : Set (SortedAssignment X U)}
    (sub : D ⊆ A) (defD : SortedDefinableOver M S.carrier D) (x : D) :
    ((f.restrict sub defD).equiv x).val = (f.equiv ⟨x.val,sub x.property⟩).val := rfl

theorem trans_apply [Finite (V .vf)] [Finite (V .rv)]
    (f : MixedGraphIso M S A B) (g : MixedGraphIso M S B C) (x : A) :
    (f.trans g).equiv x = g.equiv (f.equiv x) := rfl

theorem symm_apply (f : MixedGraphIso M S A B) (x : B) : f.symm.equiv x = f.equiv.symm x := rfl

theorem toRange_apply (f : A → SortedAssignment X V) (inj : Function.Injective f)
    (defF : DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ A, f ⟨a,h⟩ = b)) (x : A) :
    ((toRange f inj defF).equiv x).val = f x := rfl

end MixedGraphIso

end GeneralizedEuler.Section5
