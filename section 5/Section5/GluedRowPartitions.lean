module

public import Section5.RelativeRVCuts
public import Section5.RelativeFiberPartitions
public import Section5.GradedClassCuts
import all Section4.Objects

/-! A partition of every relative fiber yields the corresponding
partition of the glued RV object and preserves its graded class. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h t k : ℕ} {I : RelativeRVIndex M S h t}

namespace RelativeRVRow

theorem gluedClass_partition (A : RelativeRVRow I k) {J : Type} [Fintype J]
    (C : J → Set (SortedAssignment X A.LocusVars))
    (defC : ∀ j, SortedDefinableOver M S.carrier (C j))
    (valid : ∀ p ∈ I.labels, FiberPartitionScheme A.tags C (rvTupleAssignment p)) :
    A.gluedClass = ∑ j, (A.restrictRow (C j) (defC j)).gluedClass := by
  let W := A.object
  let D := gluedRVTags I.labels A.tags
  let Q (j : J) := gluedRVTags I.labels (C j)
  have defQ (j : J) : isRVSet M S (Q j) := gluedRVTags_definable I.definable (defC j)
  obtain ⟨e,he⟩ := A.object_carrier_equiv
  let P (j : J) (x : Fin W.arity → X .rv) := ∃ hx : x ∈ W.carrier, (e ⟨x,hx⟩).val ∈ Q j
  let B (j : J) := {x ∈ W.carrier | P j x}
  have defB (j : J) : isRVSet M S (B j) := by
    have pre := (ObjectLift.relation_of_rvGraph he).preimage (defQ j)
    unfold isRVSet
    convert W.definable.inter pre using 1
    ext a
    change (a .rv ∈ W.carrier ∧ ∃ hx : a .rv ∈ W.carrier, (e ⟨a .rv,hx⟩).val ∈ Q j) ↔
      (a .rv ∈ W.carrier ∧ ∃ y : SortedAssignment X (RVVariables (Fin (h+A.arity))),
        y .rv ∈ Q j ∧ ∃ x : W.carrier, x.val = a .rv ∧ (e x).val = y .rv)
    apply and_congr_right
    intro hx
    constructor
    · rintro ⟨_,hQ⟩
      exact ⟨rvTupleAssignment (e ⟨a .rv,hx⟩).val,hQ,⟨a .rv,hx⟩,rfl,rfl⟩
    · rintro ⟨y,hy,x,eq,ey⟩
      have same : (⟨a .rv,hx⟩ : W.carrier) = x := Subtype.ext eq.symm
      exact ⟨hx,by rw [same,ey]; exact hy⟩
  have mem (j : J) (x : W.carrier) : P j x.val ↔ (e x).val ∈ Q j :=
    ⟨fun ⟨_,hQ⟩ => hQ,fun hQ => ⟨x.property,hQ⟩⟩
  have disj : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j ne
    apply Set.disjoint_left.2
    rintro x ⟨hx,hi⟩ ⟨_,hj⟩
    have hQ := (mem i ⟨x,hx⟩).1 hi
    have hQ' := (mem j ⟨x,hx⟩).1 hj
    exact (valid _ hQ.1).2 i j ne _ ⟨hQ.2,hQ'.2⟩
  have cover : (⋃ j, B j) = W.carrier := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := Set.mem_iUnion.1 hx
      exact hj.1
    · intro hx
      have hD : (e ⟨x,hx⟩).val ∈ D := (e ⟨x,hx⟩).property
      obtain ⟨j,hj⟩ := ((valid _ hD.1).1 _).1 hD.2
      exact Set.mem_iUnion.2 ⟨j,hx,⟨hx,hD.1,hj⟩⟩
  have eq := restrictTags_partition W B defB (fun _ => Set.inter_subset_left) disj cover
  refine eq.trans (Finset.sum_congr rfl (fun j _ => ?_))
  have iso := rvDefinableEquiv_of_preserved_cut (S := S) e he (P j) (· ∈ Q j) (mem j) (defB j)
  have cut : {x ∈ D | x ∈ Q j} = gluedRVTags I.labels (A.restrictRow (C j) (defC j)).tags := by
    ext x
    exact ⟨fun ⟨⟨hp,ha⟩,_,hc⟩ => ⟨hp,ha,hc⟩,fun ⟨hp,ha,hc⟩ => ⟨⟨hp,ha⟩,hp,hc⟩⟩
  rw [cut] at iso
  exact scissors_sound M S (RVRelation.iso _ _ (iso.trans (A.restrictRow (C j) (defC j)).object_carrier_equiv.symm))

theorem gluedClass_eq_zero_of_empty (A : RelativeRVRow I k)
    (empty : ∀ p ∈ I.labels, ∀ u, appendAssignments (rvTupleAssignment p) u ∉ A.tags) :
    A.gluedClass = 0 := by
  obtain ⟨e,_⟩ := A.object_carrier_equiv
  apply scissors_sound M S
  apply RVRelation.zero
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  have h := (e ⟨x,hx⟩).property
  exact empty _ h.1 _ h.2

end RelativeRVRow

end GeneralizedEuler.Section5
