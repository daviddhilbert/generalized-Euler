module

public import Section5.MixedTaggedScissors

/-! A finite sum of VF classes is realized by the family of its
original objects with a separate tag for each summand. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.MixedTaggedFamily

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}

@[expose] def restrictTags (A : MixedTaggedFamily M S) (P : Set A.Tag) : MixedTaggedFamily M S where
  Tag := P
  coordinates t := A.coordinates t.val
  piece t := A.piece t.val
  definable t := A.definable t.val

private theorem equivalent_at_tag (B : MixedTaggedFamily M S)
    {U : TCsort → Type} (P : Set (SortedAssignment X U)) {i j : B.Tag}
    (e : i = j) (h : MixedDefinablyEquivalent M S P (B.piece j)) :
    MixedDefinablyEquivalent M S P (B.piece i) := by
  subst j
  exact h

theorem cls_eq_sum (A : MixedTaggedFamily M S) [Fintype A.Tag] :
    cls A = ∑ i, cls (single (A.piece i) (A.definable i)) := by
  classical
  have same (i : A.Tag) : MixedDefinablyEquivalent M S (A.piece i) (A.piece i) :=
    .refl (A.definable i)
  have eq (t : Finset A.Tag) :
      cls (A.restrictTags t) = ∑ i ∈ t, cls (single (A.piece i) (A.definable i)) := by
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty,← cls_empty]
      apply (cls_eq_iff _ _).2
      let D := A.restrictTags (↑(∅ : Finset A.Tag) : Set A.Tag)
      let : IsEmpty D.Tag := ⟨fun i => Finset.notMem_empty i.val i.property⟩
      exact D.iso_retag _ (Equiv.equivOfIsEmpty D.Tag Empty) (fun i => isEmptyElim i)
    | insert i t hi ih =>
      rw [Finset.sum_insert hi,← ih,← cls_append]
      apply (cls_eq_iff _ _).2
      let e : (↑(insert i t) : Set A.Tag) ≃ Unit ⊕ (↑t : Set A.Tag) :=
        { toFun := fun p => if h : p.val = i then .inl () else
            .inr ⟨p.val,(Finset.mem_insert.mp p.property).resolve_left h⟩
          invFun := Sum.elim (fun _ => ⟨i,Finset.mem_insert_self _ _⟩)
            (fun p => ⟨p.val,Finset.mem_insert_of_mem p.property⟩)
          left_inv := by intro p; dsimp; split <;> apply Subtype.ext <;> simp_all
          right_inv := by
            rintro (_|p)
            · simp
            · have ne : p.val ≠ i := fun h => hi (h ▸ p.property)
              simp [ne] }
      apply iso_retag _ _ e
      intro p
      by_cases h : p.val = i
      · have tag : e p = .inl () := by simp [e,h]
        apply equivalent_at_tag _ _ tag
        change MixedDefinablyEquivalent M S (A.piece p.val) (A.piece i)
        rw [h]
        exact same i
      · let q : (↑t : Set A.Tag) := ⟨p.val,(Finset.mem_insert.mp p.property).resolve_left h⟩
        have tag : e p = .inr q := by simp [e,h,q]
        exact equivalent_at_tag _ _ tag (same p.val)
  rw [← eq Finset.univ]
  apply (cls_eq_iff _ _).2
  let e : A.Tag ≃ (↑(Finset.univ : Finset A.Tag) : Set A.Tag) :=
    { toFun := fun i => ⟨i,Finset.mem_univ i⟩
      invFun := Subtype.val
      left_inv _ := rfl
      right_inv _ := rfl }
  exact iso_retag _ _ e same

section FieldObjects

variable [TopologicalSpace (X .vf)] {I J : Type} [Fintype I] [Fintype J]

@[expose] def fieldObjectPieces (U : I → VFObject M S) : MixedTaggedFamily M S where
  Tag := I
  coordinates i := VFVars M S (U i)
  finiteCoordinates i s := by cases s <;> exact inferInstanceAs (Finite (Fin _))
  piece i := (U i).2.carrier
  definable i := (U i).2.definable

theorem fieldObjectPieces_class (U : I → VFObject M S) :
    cls (fieldObjectPieces U) = realizeScissors (∑ i, fieldClass M S (U i)) := by
  let : Fintype (fieldObjectPieces U).Tag := inferInstanceAs (Fintype I)
  rw [cls_eq_sum,map_sum]
  exact Finset.sum_congr rfl (fun i _ => (realizeScissors_class (U i)).symm)

theorem equal_field_scissors_iso (U : I → VFObject M S) (V : J → VFObject M S)
    (h : ∑ i, fieldClass M S (U i) = ∑ j, fieldClass M S (V j)) :
    (fieldObjectPieces U).Iso (fieldObjectPieces V) := by
  apply (cls_eq_iff _ _).1
  rw [fieldObjectPieces_class,fieldObjectPieces_class,h]

end FieldObjects

end GeneralizedEuler.Section5.MixedTaggedFamily
