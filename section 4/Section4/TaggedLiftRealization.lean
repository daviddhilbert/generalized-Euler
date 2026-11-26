module

public import Section4.RVScissorRealization
public import Section4.TaggedValueClasses
import all Section4.RVFamilySemiring
import all Section4.RVFamilyOperations
import all Section4.RVTaggedEquivalence
import all Section4.ValueFactorMap
import all Section4.ValuePullback
import all Section4.Factors

/-! An equality of lifted value classes has a definable bijection between
the tagged sharp sets themselves in every degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
namespace RVFamily
variable (A : RVFamily M S)

private def restrictTags (P : Set A.Tag) : RVFamily M S where
  Tag := P
  Coord t := A.Coord t.val
  piece t := A.piece t.val
  definable t := A.definable t.val

private theorem piece_refl (t : A.Tag) : RVDefinablyEquivalent M S.carrier (A.piece t) (A.piece t) :=
  rv_reindex_equivalent M S (Equiv.refl _) _ (A.definable t)

private theorem at_equal_tag {I : Type} (D : Set (I → Z .rv)) {i j : A.Tag} (eq : i=j)
    (h : RVDefinablyEquivalent M S.carrier D (A.piece j)) : RVDefinablyEquivalent M S.carrier D (A.piece i) := by
  subst j; exact h

theorem cls_eq_sum [Fintype A.Tag] : cls A = ∑ i, cls (single (A.piece i) (A.definable i)) := by
  classical
  have eq (t : Finset A.Tag) : cls (restrictTags A t) = ∑ i ∈ t, cls (single (A.piece i) (A.definable i)) := by
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty,← cls_empty]
      let d := restrictTags A (↑(∅ : Finset A.Tag) : Set A.Tag)
      let : IsEmpty d.Tag := ⟨fun i => Finset.notMem_empty i.val i.property⟩
      exact (cls_eq_iff _ _).mpr (iso_retag d _ (Equiv.equivOfIsEmpty d.Tag Empty) (fun i => isEmptyElim i))
    | insert i t hi ih =>
      rw [Finset.sum_insert hi,← ih,← cls_append]
      apply (cls_eq_iff _ _).mpr
      let e : (↑(insert i t) : Set A.Tag) ≃ Unit ⊕ (↑t : Set A.Tag) :=
        { toFun := fun p => if h : p.val=i then .inl () else .inr ⟨p.val,(Finset.mem_insert.mp p.property).resolve_left h⟩
          invFun := Sum.elim (fun _ => ⟨i,Finset.mem_insert_self _ _⟩) (fun p => ⟨p.val,Finset.mem_insert_of_mem p.property⟩)
          left_inv := by intro p; dsimp; split <;> apply Subtype.ext <;> simp_all
          right_inv := by rintro (_|p); · simp
                          · have ne : p.val ≠ i := fun h => hi (h ▸ p.property)
                            simp [ne] }
      apply iso_retag _ _ e
      intro p
      by_cases h : p.val=i
      · have ep : e p = .inl () := by simp [e,h]
        apply at_equal_tag _ _ ep
        change RVDefinablyEquivalent M S.carrier (A.piece p.val) (A.piece i)
        rw [h]; exact piece_refl A i
      · let q : (↑t : Set A.Tag) := ⟨p.val,(Finset.mem_insert.mp p.property).resolve_left h⟩
        have ep : e p = .inr q := by simp [e,h,q]
        exact at_equal_tag _ _ ep (piece_refl A p.val)
  rw [← eq Finset.univ]
  apply (cls_eq_iff _ _).mpr
  let e : A.Tag ≃ (↑(Finset.univ : Finset A.Tag) : Set A.Tag) :=
    { toFun := fun x => ⟨x,Finset.mem_univ _⟩,invFun := Subtype.val,left_inv := fun _ => rfl,right_inv := fun _ => rfl }
  exact iso_retag _ _ e (piece_refl A)

end RVFamily

variable {J : Language} {Γ : Type*} [J.Structure Γ] (v : Z .rv → Γ) (A : Set Γ)
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  (liftIso : ∀ {k} (D E : Set (Fin k → Γ)), A.Definable J D → A.Definable J E →
    ∀ f : D ≃ E, A.Definable J {w : Fin k ⊕ Fin k → Γ | ∃ x : D, x.val = w ∘ Sum.inl ∧ (f x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent M S.carrier (sharp M v D) (sharp M v E))

@[expose] def taggedSharp {k} (U : Over (J := J) A k) : RVFamily M S where
  Tag := Fin U.tags
  Coord _ := Fin k
  piece i := sharp M v (U.piece i)
  definable i := defSharp (U.isDefinable i)

theorem realize_tagged_lift {k} (U : Over (J := J) A k) :
    RVFamily.realizeScissors M S (valueFactorHom M S v A defSharp liftIso (taggedValueClass A U)) =
    (taggedSharp v A defSharp U).cls := by
  let : Fintype (taggedSharp v A defSharp U).Tag := inferInstanceAs (Fintype (Fin U.tags))
  rw [RVFamily.cls_eq_sum (taggedSharp v A defSharp U),taggedValueClass_eq_sum,map_sum,map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [valueFactorHom_piece,RVFamily.realizeScissors_class]; rfl

theorem tagged_lift_iso_of_class_eq {k} (U W : Over (J := J) A k)
    (h : valueFactorHom M S v A defSharp liftIso (taggedValueClass A U) =
      valueFactorHom M S v A defSharp liftIso (taggedValueClass A W)) :
    (taggedSharp v A defSharp U).Iso (taggedSharp v A defSharp W) := by
  apply (RVFamily.cls_eq_iff _ _).mp
  simpa only [← realize_tagged_lift v A defSharp liftIso] using congrArg (RVFamily.realizeScissors M S) h

end GeneralizedEuler.Section4
