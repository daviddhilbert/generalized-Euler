module

public import Section5.GradedFamilyIsomorphism
public import Section5.ObjectLiftRestrictions
import all Section4.FiniteScissors

/-! Split both sides of a graded class equality into the rectangles of
the graph on the tags. This preserves the structure maps on each cut. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}

theorem restrictTags_partition (U : RVObject M S k) {I : Type} [Fintype I]
    (A : I → Set (Fin U.arity → X .rv)) (hA : ∀ i, isRVSet M S (A i))
    (sub : ∀ i, A i ⊆ U.carrier) (disj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (cover : (⋃ i, A i) = U.carrier) :
    objectClass M S ⟨k,U⟩ = ∑ i, objectClass M S ⟨k,ObjectLift.restrictTags U (sub i) (hA i)⟩ := by
  refine (objectClass_partition U A hA disj cover).trans (Finset.sum_congr rfl fun i _ => ?_)
  apply scissors_sound M S
  apply RVRelation.iso
  change RVDefinablyEquivalent M S.carrier (A i) (A i)
  exact ⟨Equiv.refl _,definable_identity_label M S (hA i)⟩

/-- The tagged union of a disjoint subfamily may be represented by a
single restriction of the original structure map. -/
theorem restrictTags_union_class (U : RVObject M S k) {I : Type} [Fintype I]
    (A : I → Set (Fin U.arity → X .rv)) (defA : ∀ i, isRVSet M S (A i))
    (sub : ∀ i, A i ⊆ U.carrier) (disj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    objectClass M S ⟨k,ObjectLift.restrictTags U (Set.iUnion_subset sub) (isRVSet_iUnion defA)⟩ =
      ∑ i, objectClass M S ⟨k,ObjectLift.restrictTags U (sub i) (defA i)⟩ := by
  let V := ObjectLift.restrictTags U (Set.iUnion_subset sub) (isRVSet_iUnion defA)
  have eq := restrictTags_partition V A defA (Set.subset_iUnion A) disj rfl
  refine eq.trans (Finset.sum_congr rfl fun i _ => ?_)
  apply scissors_sound M S
  apply RVRelation.iso
  change RVDefinablyEquivalent M S.carrier (A i) (A i)
  exact ⟨Equiv.refl _,definable_identity_label M S (defA i)⟩

section Family

variable {I J : Type} [Fintype I] [Fintype J]
  (U : I → GradedObject M S) (V : J → GradedObject M S)
  (e : (taggedGradedFamily M S U).Points ≃ (taggedGradedFamily M S V).Points)
  (graph : ∀ i j, isRVSet M S (RVFamily.graphPiece
    (taggedGradedFamily M S U) (taggedGradedFamily M S V) e i j))

@[expose] def sourceCutObject (i : I) (j : J) : RVObject M S (U i).1 :=
  ObjectLift.restrictTags (U i).2
    (sourceGraphCut_subset (taggedGradedFamily M S U) (taggedGradedFamily M S V) e i j)
    (sourceGraphCut_definable (taggedGradedFamily M S U) (taggedGradedFamily M S V) e i j (graph i j))

theorem sourceCutObject_sum (i : I) :
    objectClass M S (U i) = ∑ j, objectClass M S ⟨(U i).1,sourceCutObject U V e graph i j⟩ := by
  obtain ⟨disj,cover⟩ := sourceGraphCut_partition
    (taggedGradedFamily M S U) (taggedGradedFamily M S V) e i
  exact restrictTags_partition (U i).2 _ _ _ disj cover

theorem sourceCutObject_match
    (preserve : ∀ x, (V (e x).1).1 = (U x.1).1) (i : I) (j : J) :
    objectClass M S ⟨(U i).1,sourceCutObject U V e graph i j⟩ =
      objectClass M S ⟨(V j).1,sourceCutObject V U e.symm
        (RVFamily.inverse_graph _ _ e graph) j i⟩ := by
  let A := sourceCutObject U V e graph i j
  let B := sourceCutObject V U e.symm (RVFamily.inverse_graph _ _ e graph) j i
  have iso := sourceGraphCut_equivalent (taggedGradedFamily M S U)
    (taggedGradedFamily M S V) e i j (graph i j)
  change RVDefinablyEquivalent M S.carrier A.carrier B.carrier at iso
  by_cases degree : (V j).1 = (U i).1
  · let d := (U i).1
    have same {d' : ℕ} (B' : RVObject M S d') (eq : d' = d)
        (iso' : RVDefinablyEquivalent M S.carrier A.carrier B'.carrier) :
        objectClass M S ⟨d,A⟩ = objectClass M S ⟨d',B'⟩ := by
      subst d'
      exact scissors_sound M S (RVRelation.iso _ _ iso')
    exact same B degree iso
  · have emptyA : A.carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro _ ⟨x,_,he⟩
      have h := preserve ⟨i,x⟩
      rw [he] at h
      exact degree h
    have emptyB : B.carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact Set.eq_empty_iff_forall_notMem.1 emptyA _ (iso.choose.symm ⟨x,hx⟩).property
    exact (scissors_sound M S (RVRelation.zero A emptyA)).trans
      (scissors_sound M S (RVRelation.zero B emptyB)).symm

end Family

end GeneralizedEuler.Section5
