module

public import Section4.RestrictedBijections
public import Section4.PositivePresentations
import all Section4.RestrictedBijections
import all Section4.TaggedObjects
import all Section4.SignPieces
import all Section4.FiniteScissors
import all Section4.Objects
import all Section4.RectangleClasses

/-! A partition of the original object, with an actual fixed-base bijection
from each cell to a positive set in the degree of the structure map. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {J : Language} {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [J.Structure K] (O : ValuationSubring K) [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

theorem positive_object_cover {k} (U : RVObject _ S k) (minus : rv O (-1) ∈ S.carrier .rv)
    (sat : ∀ D : ℕ → Set (Fin k → RV0 O), (∀ i, isRVSet _ S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) :
    ∃ (N : ℕ) (A : Fin N → Set (Fin U.arity → RV0 O)) (B : Fin N → Set (Fin k → RV0 O)),
      (∀ i, isRVSet _ S (A i)) ∧ (∀ i, isRVSet _ S (B i)) ∧
      (∀ i x, x ∈ B i → ∀ j, IsPositiveRV O (x j)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧ (⋃ i, A i) = U.carrier ∧
      ∀ i, RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (A i) (B i) := by
  classical
  let := rvLinearOrder O hO
  let M := canonicalStructure (L := J) O hO P
  let lt (x y : Fin U.arity → RV0 O) := toLex x < toLex y
  have hl := canonical_lex_definable (J := J) O hO P S (n := U.arity)
  obtain ⟨N,disj,cover⟩ := U.tag_partition lt sat
  let A (i : Fin N) := U.tagPiece lt i.val
  let W (i : Fin N) := U.restrict (A := A i) (fun _ h => h.1) (U.tagPiece_definable lt hl i.val)
  let T (i : Fin N) := Set.range (W i).label
  have hd (i) : isRVSet M S (T i) := (W i).labelImage.definable
  have inj (i) : Function.Injective (W i).label := U.tagPiece_injective lt (fun h h' => lt_trans h h')
    (fun _ => lt_irrefl _) (fun x y ne => lt_or_gt_of_ne (fun h => ne (toLex.injective h))) i.val
  let e (i) := Equiv.ofInjective (W i).label (inj i)
  let signs (i : Fin N) b := signPiece O hO (T i) b
  let C i b := rvPreimage (e i) (signs i b)
  let B i b := positiveSignImage O hO (T i) b
  have slice i b := restricted_rvGraph (M := M) (S := S) (e i) (W i).graph (signs i b)
    (signPiece_definable O hO P S (T i) (hd i) b) (fun _ h => h.1)
  have bij i b : RVDefinablyEquivalent M S.carrier (C i b) (B i b) :=
    (slice i b).2.trans (signPiece_normalize O hO P S (T i) (hd i) minus b)
  have row (i : Fin N) : Pairwise (fun b c => Disjoint (C i b) (C i c)) ∧ (⋃ b, C i b) = A i := by
    apply rvPreimage_partition
    · intro b c ne
      exact Set.disjoint_left.mpr fun _ hb hc => ne (hb.2.symm.trans hc.2)
    · ext x; rw [Set.mem_iUnion]
      exact ⟨fun ⟨_,h⟩ => h.1,fun hx => ⟨_,(signPiece_unique O hO (T i) x hx).choose_spec.1⟩⟩
  let idx := (Fintype.equivFin (Fin N × (Fin k → Bool))).symm
  have sub i b : C i b ⊆ A i := fun _ h => by obtain ⟨x,rfl,_⟩ := h; exact x.property
  refine ⟨_,fun j => C (idx j).1 (idx j).2,fun j => B (idx j).1 (idx j).2,fun j => (slice _ _).1,
    fun j => rv_equivalent_target_definable (bij _ _),?_,?_,?_,fun j => bij _ _⟩
  · intro j
    refine positiveSignImage_positive O hO (T (idx j).1) ?_ _
    rintro _ ⟨z,rfl⟩ i; exact (W (idx j).1).nonzero z i
  · intro i j ne
    by_cases h : (idx i).1 = (idx j).1
    · have bne : (idx i).2 ≠ (idx j).2 := fun h' => ne (idx.injective (Prod.ext h h'))
      change Disjoint (C (idx i).1 (idx i).2) (C (idx j).1 (idx j).2)
      rw [← h]; exact (row (idx i).1).1 bne
    · exact (disj h).mono (sub _ _) (sub _ _)
  · ext x
    change (x ∈ ⋃ j, C (idx j).1 (idx j).2) ↔ x ∈ U.carrier
    have member : x ∈ U.carrier ↔ ∃ i, x ∈ A i := (congrArg (x ∈ ·) cover).to_iff.symm.trans Set.mem_iUnion
    refine Set.mem_iUnion.trans (Iff.trans ?_ member.symm)
    constructor
    · rintro ⟨j,h⟩; exact ⟨_,sub _ _ h⟩
    · rintro ⟨i,hi⟩
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp ((congrArg (x ∈ ·) (row i).2).mpr hi)
      refine ⟨idx.symm (i,b),?_⟩
      change x ∈ C (idx (idx.symm (i,b))).1 (idx (idx.symm (i,b))).2
      rw [idx.apply_symm_apply]; exact hb

end GeneralizedEuler.Section4
