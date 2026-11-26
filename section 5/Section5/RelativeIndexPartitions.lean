module

public import Section5.GluedRowPartitions
public import Section5.RelativeObjectFamilies
import all Section4.Objects

/-! Cutting the retained index by a definable partition cuts the
glued class. Each part keeps the original selected coordinates. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h t k : ℕ} {D : RelativeRVIndex M S h t}

namespace RelativeRVIndex

@[expose] def restrict (D : RelativeRVIndex M S h t)
    (C : Set (Fin h → X .rv)) (defC : isRVSet M S C) : RelativeRVIndex M S h t where
  labels := D.labels ∩ C
  definable := D.definable.inter defC
  select := D.select
  active p hp := D.active p hp.1
  finite v := (D.finite v).subset fun _ h => ⟨h.1.1,h.2⟩

end RelativeRVIndex

namespace RelativeRVRow

variable (A : RelativeRVRow D k)

@[expose] def onIndexPiece (C : Set (Fin h → X .rv)) (defC : isRVSet M S C) :
    RelativeRVRow (D.restrict C defC) k :=
  ⟨A.arity,A.tags,A.tagsDefinable,A.graph,A.graphDefinable,fun p hp => A.valid p hp.1⟩

@[expose] def indexLocus (C : Set (Fin h → X .rv)) : Set (SortedAssignment X A.LocusVars) :=
  A.tags ∩ {a | a .rv ∘ Sum.inl ∈ C}

theorem indexLocus_definable {C : Set (Fin h → X .rv)} (defC : isRVSet M S C) :
    SortedDefinableOver M S.carrier (A.indexLocus C) :=
  A.tagsDefinable.inter (defC.pullback_relabel (fun _ => Sum.inl))

theorem gluedClass_restrict_index (C : Set (Fin h → X .rv)) (defC : isRVSet M S C) :
    (A.restrictRow (A.indexLocus C) (A.indexLocus_definable defC)).gluedClass = (A.onIndexPiece C defC).gluedClass := by
  let U := A.restrictRow (A.indexLocus C) (A.indexLocus_definable defC)
  let V := A.onIndexPiece C defC
  have eq : gluedRVTags D.labels U.tags = gluedRVTags (D.restrict C defC).labels V.tags := by
    ext a
    change (a ∘ rvHead ∈ D.labels ∧ (appendAssignments (rvTupleAssignment (a ∘ rvHead))
      (rvTupleAssignment (a ∘ rvTail)) ∈ A.tags ∧
      appendAssignments (rvTupleAssignment (a ∘ rvHead)) (rvTupleAssignment (a ∘ rvTail)) ∈ A.indexLocus C)) ↔ _
    constructor
    · rintro ⟨hp,ht,_,hc⟩
      exact ⟨⟨hp,hc⟩,ht⟩
    · rintro ⟨⟨hp,hc⟩,ht⟩
      exact ⟨hp,ht,ht,hc⟩
  have iso := U.object_carrier_equiv
  rw [eq] at iso
  apply scissors_sound M S
  exact RVRelation.iso U.object V.object (iso.trans V.object_carrier_equiv.symm)

theorem gluedClass_index_partition {J : Type} [Fintype J] (C : J → Set (Fin h → X .rv))
    (defC : ∀ j, isRVSet M S (C j))
    (disj : Pairwise (fun i j => Disjoint (C i) (C j))) (cover : D.labels ⊆ ⋃ j, C j) :
    A.gluedClass = ∑ j, (A.onIndexPiece (C j) (defC j)).gluedClass := by
  have valid p (hp : p ∈ D.labels) : FiberPartitionScheme A.tags (fun j => A.indexLocus (C j)) (rvTupleAssignment p) := by
    constructor
    · intro u
      constructor
      · intro hu
        obtain ⟨j,hj⟩ := Set.mem_iUnion.1 (cover hp)
        exact ⟨j,hu,hj⟩
      · rintro ⟨j,hj,_⟩
        exact hj
    · intro i j ne u both
      exact Set.disjoint_left.1 (disj ne) both.1.2 both.2.2
  refine (A.gluedClass_partition (fun j => A.indexLocus (C j)) (fun j => A.indexLocus_definable (defC j))
    valid).trans (Finset.sum_congr rfl fun j _ => A.gluedClass_restrict_index (C j) (defC j))

end RelativeRVRow

namespace RelativeObjectFamily

theorem gluedClass_index_partition {I J : Type} [Fintype I] [Fintype J]
    (D : RelativeRVIndex M S h t) (A : RelativeObjectFamily M S (RVVariables (Fin h)) I)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (v : ∀ p ∈ D.labels, Valid A zero (rvTupleAssignment p))
    (C : J → Set (Fin h → X .rv)) (defC : ∀ j, isRVSet M S (C j))
    (disj : Pairwise (fun i j => Disjoint (C i) (C j))) (cover : D.labels ⊆ ⋃ j, C j) :
    gluedClass zero hz D A v =
      ∑ j, gluedClass zero hz (D.restrict (C j) (defC j)) A (fun p hp => v p hp.1) := by
  unfold gluedClass
  refine (Finset.sum_congr rfl (fun i _ =>
    ((A i).row zero hz D (fun p hp => v p hp i)).gluedClass_index_partition C defC disj cover)).trans ?_
  exact Finset.sum_comm

end RelativeObjectFamily

end GeneralizedEuler.Section5
