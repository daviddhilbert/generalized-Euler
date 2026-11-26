module

public import Section5.RVAppendLabel

/-! Adjoining specified coordinates of an RV tuple gives its definable
graph. Projection to the original tuple is the inverse isomorphism. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {I J : Type} [Finite I] [Finite J]

theorem rv_equiv_record_coordinates (D : Set (I → X .rv)) (defD : isRVSet M S D)
    (select : J → I) :
    RVDefinablyEquivalent M S.carrier D
      {w : J ⊕ I → X .rv | w ∘ Sum.inr ∈ D ∧ w ∘ Sum.inl = w ∘ Sum.inr ∘ select} := by
  let C := {w : J ⊕ I → X .rv | w ∘ Sum.inr ∈ D ∧ w ∘ Sum.inl = w ∘ Sum.inr ∘ select}
  let f : D ≃ C :=
    { toFun := fun a => ⟨Sum.elim (a.val ∘ select) a.val,a.property,rfl⟩
      invFun := fun b => ⟨b.val ∘ Sum.inr,b.property.1⟩
      left_inv := fun _ => rfl
      right_inv := by
        intro b
        apply Subtype.ext
        funext j
        cases j with
        | inl j => exact (congrFun b.property.2 j).symm
        | inr j => rfl }
  refine ⟨f,?_⟩
  let W := RVVariables (I ⊕ (J ⊕ I))
  let old : (s : TCsort) → RVVariables I s → W s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  have new := SortedDefinableOver.iInter (fun j : J => SortedDefinableOver.coordinate_eq
    (M := M) (A := S.carrier) (Var := W) .rv (.inl (select j)) (.inr (.inl j)))
  have tail := SortedDefinableOver.iInter (fun i : I => SortedDefinableOver.coordinate_eq
    (M := M) (A := S.carrier) (Var := W) .rv (.inl i) (.inr (.inr i)))
  convert (defD.pullback_relabel old).inter (new.inter tail) using 1
  ext a
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change (∃ x : D, x.val = a .rv ∘ Sum.inl ∧ (f x).val = a .rv ∘ Sum.inr) ↔
    (a .rv ∘ Sum.inl ∈ D ∧ (∀ j, a .rv (.inl (select j)) = a .rv (.inr (.inl j))) ∧
      (∀ i, a .rv (.inl i) = a .rv (.inr (.inr i))))
  constructor
  · rintro ⟨x,hx,he⟩
    refine ⟨hx ▸ x.property,fun j => ?_,fun i => ?_⟩
    · exact (congrFun hx _).symm.trans (congrFun he (.inl j))
    · exact (congrFun hx _).symm.trans (congrFun he (.inr i))
  · rintro ⟨ha,hn,ht⟩
    refine ⟨⟨_,ha⟩,rfl,?_⟩
    funext j
    cases j with
    | inl j => exact hn j
    | inr j => exact ht j

end GeneralizedEuler.Section5
