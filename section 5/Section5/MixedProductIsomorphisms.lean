module

public import Section5.MixedTaggedOperations

/-! Fixed-base mixed isomorphisms preserve ordinary Cartesian products. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.MixedDefinablyEquivalent

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {U V W Z : TCsort → Type}

theorem product {A : Set (SortedAssignment X U)} {B : Set (SortedAssignment X V)}
    {C : Set (SortedAssignment X W)} {D : Set (SortedAssignment X Z)}
    (left : MixedDefinablyEquivalent M S A B) (right : MixedDefinablyEquivalent M S C D) :
    MixedDefinablyEquivalent M S (mixedProduct A C) (mixedProduct B D) := by
  obtain ⟨e,de⟩ := left
  obtain ⟨f,df⟩ := right
  let pack := MixedTaggedFamily.productPoints B D
  let t := (MixedTaggedFamily.productPoints A C).symm.trans ((Equiv.prodCongr e f).trans pack)
  refine ⟨t,?_⟩
  let Out := SumVariables (SumVariables U W) (SumVariables V Z)
  let pl (s : TCsort) : SumVariables U V s → Out s := Sum.map Sum.inl Sum.inl
  let pr (s : TCsort) : SumVariables W Z s → Out s := Sum.map Sum.inr Sum.inr
  unfold DefinableRelation at de df ⊢
  convert (de.pullback_relabel pl).inter (df.pullback_relabel pr) using 1
  ext a
  let x : SortedAssignment X (SumVariables U W) := fun s => a s ∘ Sum.inl
  let y : SortedAssignment X (SumVariables V Z) := fun s => a s ∘ Sum.inr
  change (∃ h : x ∈ mixedProduct A C, (t ⟨x,h⟩).val = y) ↔
    (∃ hx : (fun s => x s ∘ Sum.inl) ∈ A, (e ⟨_,hx⟩).val = (fun s => y s ∘ Sum.inl)) ∧
    (∃ hx : (fun s => x s ∘ Sum.inr) ∈ C, (f ⟨_,hx⟩).val = (fun s => y s ∘ Sum.inr))
  constructor
  · rintro ⟨h,eq⟩
    have eqL := congrArg (fun z : SortedAssignment X (SumVariables V Z) => fun s => z s ∘ Sum.inl) eq
    have eqR := congrArg (fun z : SortedAssignment X (SumVariables V Z) => fun s => z s ∘ Sum.inr) eq
    exact ⟨⟨h.1,eqL⟩,⟨h.2,eqR⟩⟩
  · rintro ⟨⟨hl,el⟩,hr,er⟩
    refine ⟨⟨hl,hr⟩,?_⟩
    funext s i
    cases i with
    | inl i => exact congrFun (congrFun el s) i
    | inr i => exact congrFun (congrFun er s) i

end GeneralizedEuler.Section5.MixedDefinablyEquivalent
