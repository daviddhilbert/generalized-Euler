module

public import Section4.SignPieces
import all Section4.SignPieces
import all Section4.FiniteScissors
import all Section4.TaggedObjects
import all Section4.Objects
import all Section2.RVDefinableEquivalence

/-! Positive identity-labelled generators for every graded RV object. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {J : Language} {E K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [J.Structure K] (O : ValuationSubring K) [J.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : E → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

def identityRVObject {L : Language} {E : Type*} {Z : TCsort → Type*}
    {M : SortedStructure L E Z} {C : SortedSubstructure M} {k}
    (D : Set (Fin k → Z .rv)) (hd : isRVSet M C D)
    (nz : ∀ x ∈ D, ∀ i, x i ≠ M.funMap .rvZero (fun j => j.elim0)) : RVObject M C k :=
  ⟨k,D,hd,Subtype.val,definable_identity_label M C hd,fun x => nz _ x.property,
    fun y => (Set.finite_singleton y).preimage Subtype.val_injective.injOn⟩

def positiveObject {k} (D : Set (Fin k → RV0 O)) (hd : isRVSet _ S D)
    (pos : ∀ x ∈ D, ∀ i, IsPositiveRV O (x i)) : RVObject _ S k :=
  identityRVObject D hd (fun x hx i => (pos x hx i).ne_zero O)

theorem positive_object_classes {k} (U : RVObject _ S k) (minus : rv O (-1) ∈ S.carrier .rv)
    (sat : ∀ D : ℕ → Set (Fin k → RV0 O), (∀ i, isRVSet _ S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) :
    ∃ (l : ℕ) (D : Fin l → (Fin k → Bool) → Set (Fin k → RV0 O))
      (hd : ∀ i b, isRVSet _ S (D i b))
      (pos : ∀ i b x, x ∈ D i b → ∀ j, IsPositiveRV O (x j)),
      objectClass _ S ⟨k,U⟩ = ∑ i, ∑ b, objectClass _ S ⟨k,positiveObject O hO P S _ (hd i b) (pos i b)⟩ := by
  classical
  let M := canonicalStructure (L := J) O hO P
  obtain ⟨l,V,_,labels,hu⟩ := canonical_tagged_presentation O hO P S U sat
  let T (i : Fin l) := (V i).labelImage
  have inj (i) : Function.Injective (V i).label := by
    obtain ⟨h,eq⟩ := labels i
    intro x y hxy
    apply Subtype.ext
    funext j
    have a := congrFun hxy (Fin.cast h j)
    simpa [eq] using a
  let A (i : Fin l) := Set.range (V i).label
  have ha (i) : isRVSet M S (A i) := (T i).definable
  have nz (i) (x : Fin k → RV0 O) (hx : x ∈ A i) (j) : x j ≠ 0 := by
    obtain ⟨z,rfl⟩ := hx
    exact (V i).nonzero z j
  let parts i b := signPiece O hO (A i) b
  let D i b := positiveSignImage O hO (A i) b
  have eqv (i b) : RVDefinablyEquivalent M S.carrier (parts i b) (D i b) :=
    signPiece_normalize O hO P S (A i) (ha i) minus b
  have hd (i b) : isRVSet M S (D i b) := by
    obtain ⟨e,he⟩ := eqv i b
    have eq : D i b = Set.range (fun x => (e x).val) := by
      ext y
      exact ⟨fun hy => ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩,
        fun ⟨x,hx⟩ => hx ▸ (e x).property⟩
    rw [eq]
    exact definable_range_of_rvGraph _ he
  have pos i b := positiveSignImage_positive O hO (A i) (fun x hx j => nz i x hx j) b
  refine ⟨_,D,hd,pos,hu.trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  have cover : ⋃ b, parts i b = (T i).carrier := by
    ext x; rw [Set.mem_iUnion]
    exact ⟨fun ⟨_,h⟩ => h.1,fun hx => ⟨_,(signPiece_unique O hO (A i) x hx).choose_spec.1⟩⟩
  have disj : Pairwise (fun b c => Disjoint (parts i b) (parts i c)) := fun _ _ ne =>
    Set.disjoint_left.mpr fun _ hb hc => ne (hb.2.symm.trans hc.2)
  have cut := objectClass_partition (T i) (parts i) (signPiece_definable O hO P S (A i) (ha i)) disj cover
  refine ((RVObject.labelImage_class (V i) (inj i)).trans cut).trans (Finset.sum_congr rfl fun b _ => ?_)
  exact scissors_sound M S (RVRelation.iso _ _ (eqv i b))

end GeneralizedEuler.Section4
