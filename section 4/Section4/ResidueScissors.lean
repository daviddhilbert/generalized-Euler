module

public import Section4.FiniteScissors
import all Section4.FiniteScissors
import all Section4.Factors
import all Section4.Objects

/-! Cuts and coordinate changes in the residue category at their original degrees. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 MvPolynomial
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
  {M : SortedStructure L E Z} {S : SortedSubstructure M} {Γ : Type*} {v : Z .rv → Γ}

def residueClass {k} (U : RVObject M S k) (hu : U.IsResidue M S v) : ResidueSemiring M S v :=
  (ringConGen (residueRelation M S v)).mk' (X ⟨⟨k,U⟩,hu⟩)

theorem residue_class_iso {k} (U V : RVObject M S k) (hu : U.IsResidue M S v)
    (hv : V.IsResidue M S v) (e : U.Isomorphic M S V) :
    residueClass U hu = residueClass V hv := by
  apply Quotient.sound
  apply RingConGen.Rel.of
  simpa [residueRelation] using RVRelation.iso U V e

theorem residue_class_zero {k} (U : RVObject M S k) (hu : U.IsResidue M S v)
    (h : U.carrier = ∅) : residueClass U hu = 0 := by
  apply Quotient.sound
  apply RingConGen.Rel.of
  simpa [residueRelation] using RVRelation.zero U h

theorem residue_class_cut {k} (U V W : RVObject M S k) (hu : U.IsResidue M S v)
    (hv : V.IsResidue M S v) (hw : W.IsResidue M S v) (A B : Set (Fin U.arity → Z .rv))
    (ha : isRVSet M S A) (hb : isRVSet M S B) (disj : Disjoint A B) (cover : A ∪ B = U.carrier)
    (ea : RVDefinablyEquivalent M S.carrier A V.carrier)
    (eb : RVDefinablyEquivalent M S.carrier B W.carrier) :
    residueClass U hu = residueClass V hv + residueClass W hw := by
  apply Quotient.sound
  apply RingConGen.Rel.of
  simpa [residueRelation] using RVRelation.cut U V W A B ha hb disj cover ea eb

theorem residue_class_product {k l} (U : RVObject M S k) (V : RVObject M S l)
    (W : RVObject M S (k+l)) (hu : U.IsResidue M S v) (hv : V.IsResidue M S v)
    (hw : W.IsResidue M S v)
    (e : RVDefinablyEquivalent M S.carrier (productSet U.carrier V.carrier) W.carrier) :
    residueClass W hw = residueClass U hu * residueClass V hv := by
  apply Quotient.sound
  apply RingConGen.Rel.of
  simpa [residueRelation] using RVRelation.prod U V W e

theorem residue_class_partition {k} (U : RVObject M S k) (hu : U.IsResidue M S v)
    {I : Type} [Fintype I] (A : I → Set (Fin U.arity → Z .rv)) (ha : ∀ i, isRVSet M S (A i))
    (disj : Pairwise (fun i j => Disjoint (A i) (A j))) (cover : ⋃ i, A i = U.carrier) :
    residueClass U hu = ∑ i, residueClass (U.restrict (cover ▸ Set.subset_iUnion A i) (ha i))
      (U.restrict_residue v hu _ _) := by
  let P (D : Set (Fin U.arity → Z .rv)) := D ⊆ U.carrier ∧ isRVSet M S D
  let b (D) (h : P D) := residueClass (U.restrict h.1 h.2) (U.restrict_residue v hu _ _)
  have h0 : P ∅ := ⟨Set.empty_subset _,⟨.falsum,fun _ => Iff.rfl⟩⟩
  have add {D E} (hD : P D) (hE : P E) : P (D ∪ E) :=
    ⟨Set.union_subset hD.1 hE.1,hD.2.union hE.2⟩
  have cut (D E) (hD : P D) (hE : P E) (h : Disjoint D E) :
      b (D ∪ E) (add hD hE) = b D hD + b E hE :=
    residue_class_cut _ _ _ _ _ _ D E hD.2 hE.2 h rfl
      ⟨Equiv.refl _,definable_identity_label M S hD.2⟩
      ⟨Equiv.refl _,definable_identity_label M S hE.2⟩
  obtain ⟨h,eq⟩ := finite_scissor_sum b h0
    (residue_class_zero _ _ rfl) @add cut A (fun i => ⟨cover ▸ Set.subset_iUnion A i,ha i⟩) disj
  apply Eq.trans _ eq
  apply residue_class_iso
  change RVDefinablyEquivalent M S.carrier U.carrier (⋃ i, A i)
  rw [cover]
  exact ⟨Equiv.refl _,definable_identity_label M S U.definable⟩

end GeneralizedEuler.Section4
