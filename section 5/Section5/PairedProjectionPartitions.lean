module

public import Section5.FieldLiftPartitions
public import Section5.LabelProjection

/-! Refine the source and target projection partitions simultaneously. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n k : ℕ} {U V : Set (labelAssignment n X)}

/-- Lift each paired projection piece and glue the results on the full
field pullbacks. Source points are indexed by both their own piece and
the piece containing their images. -/
theorem definable_lift_of_paired_projections {I J : Type*} [Finite I] [Finite J]
    (e : U ≃ V)
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b))
    (P : I → Set (labelAssignment n X)) (Q : J → Set (labelAssignment n X))
    (hP : ∀ i, SortedDefinableOver M S.carrier (P i))
    (hQ : ∀ j, SortedDefinableOver M S.carrier (Q j))
    (p : I → Fin k ↪ Fin n) (q : J → Fin k ↪ Fin n)
    (pinj : ∀ i, Set.InjOn (projectLabels (p i)) (P i))
    (qinj : ∀ j, Set.InjOn (projectLabels (q j)) (Q j))
    (pDisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (qDisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (pCover : (⋃ i, P i) = U) (qCover : (⋃ j, Q j) = V)
    (pieces : ∀ (A : Set U), SortedDefinableOver M S.carrier (Subtype.val '' A) →
      ∀ (p q : Fin k ↪ Fin n), Set.InjOn (projectLabels p) (Subtype.val '' A) →
      Set.InjOn (projectLabels q) (Subtype.val '' (e '' A)) →
      HasDefinableFieldLift S (restrictedLabelEquiv e A)) :
    HasDefinableFieldLift S e := by
  let A (ij : I × J) : Set U := {a | a.val ∈ P ij.1 ∧ (e a).val ∈ Q ij.2}
  have hCover (u : U) : ∃ ij, u ∈ A ij := by
    have hp : u.val ∈ ⋃ i, P i := by rw [pCover]; exact u.property
    have hq : (e u).val ∈ ⋃ j, Q j := by rw [qCover]; exact (e u).property
    obtain ⟨i,hi⟩ := Set.mem_iUnion.1 hp
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 hq
    exact ⟨(i,j),hi,hj⟩
  have hDisj : Pairwise (fun ij ij' => Disjoint (A ij) (A ij')) := by
    intro ij ij' ne
    refine Set.disjoint_left.2 ?_
    intro x hx hx'
    by_cases eq : ij.1 = ij'.1
    · have hne : ij.2 ≠ ij'.2 := fun eq' => ne (Prod.ext eq eq')
      exact Set.disjoint_left.1 (qDisj hne) hx.2 hx'.2
    · exact Set.disjoint_left.1 (pDisj eq) hx.1 hx'.1
  apply definable_lift_of_label_partition e A hDisj hCover
  intro ij
  have eq : Subtype.val '' A ij = P ij.1 ∩ rvPreimage e (Q ij.2) := by
    ext a
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu.1,u.property,hu.2⟩
    · rintro ⟨ha,hu,he⟩
      exact ⟨⟨a,hu⟩,⟨ha,he⟩,rfl⟩
  have hD : SortedDefinableOver M S.carrier (Subtype.val '' A ij) := by
    rw [eq]
    exact (hP ij.1).inter (rvPreimage_definable e hE (hQ ij.2))
  apply pieces (A ij) hD (p ij.1) (q ij.2)
  · rw [eq]
    exact (pinj ij.1).mono Set.inter_subset_left
  · apply (qinj ij.2).mono
    rintro _ ⟨_,⟨u,hu,rfl⟩,rfl⟩
    exact hu.2

end GeneralizedEuler.Section5
