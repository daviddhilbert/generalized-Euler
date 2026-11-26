module

public import Section5.DefinableProjection
public import Section5.VerticalCenters

/-! Uniform fixed-base covers obtained from saturation. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {V : TCsort → Type}

/-- A pointwise cover by definable sets has a finite subcover on any
fixed-base definable domain. -/
theorem finite_definable_cover {I : Type*}
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier V)
      (BaseAssignments S.carrier V))
    (A : Set (SortedAssignment X V)) (hA : SortedDefinableOver M S.carrier A)
    (B : I → Set (SortedAssignment X V)) (hB : ∀ i, SortedDefinableOver M S.carrier (B i))
    (cover : ∀ x ∈ A, ∃ i, x ∈ B i) :
    ∃ C : Finset I, ∀ x ∈ A, ∃ i ∈ C, x ∈ B i := by
  classical
  obtain ⟨φ,hφ⟩ := hA
  choose ψ hψ using hB
  obtain ⟨C,hC⟩ := finite_tests M (WithBase S.carrier V) (BaseAssignments S.carrier V)
    sat φ (fun i => (ψ i).neg) (by
      intro v hv hTests hIn
      let x : SortedAssignment X V := fun s i => v s (.inr i)
      have eq : v = fun s => Sum.elim Subtype.val (x s) := by
        funext s t
        rcases t with t | t
        · exact hv s t
        · rfl
      rw [eq] at hTests hIn
      obtain ⟨i,hi⟩ := cover x ((hφ x).2 hIn)
      exact ((ψ i).realize_neg M _).1 (hTests i) ((hψ i x).1 hi))
  refine ⟨C,?_⟩
  intro x hx
  by_contra! hn
  let v (s : TCsort) := Sum.elim (Subtype.val : S.carrier s → X s) (x s)
  exact hC v (fun _ _ => rfl)
    (fun i hi => ((ψ i).realize_neg M v).2 (fun ht => hn i hi ((hψ i x).2 ht))) ((hφ x).1 hx)

/-- A finite definable cover can be made disjoint by retaining the first
piece containing the point. Each new piece lies in the corresponding
original piece. -/
theorem disjoint_definable_subcover {I : Type*} [Finite I]
    (D : I → Set (SortedAssignment X V)) (hD : ∀ i, SortedDefinableOver M S.carrier (D i)) :
    ∃ P : I → Set (SortedAssignment X V),
      (∀ i, SortedDefinableOver M S.carrier (P i)) ∧
      (∀ i, P i ⊆ D i) ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = ⋃ i, D i := by
  classical
  let := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let P (i : I) := D i ∩ {x | ∀ j : I, e j < e i → x ∉ D j}
  have hPrev (i : I) : SortedDefinableOver M S.carrier {x | ∀ j : I, e j < e i → x ∉ D j} := by
    have h := SortedDefinableOver.iInter (fun j : {j : I // e j < e i} => (hD j.val).compl)
    convert h using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, Subtype.forall]
  refine ⟨P,fun i => (hD i).inter (hPrev i),fun i => Set.inter_subset_left,?_,?_⟩
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    intro x hi hj
    rcases lt_or_gt_of_ne (fun he => hij (e.injective he)) with h | h
    · exact hj.2 i h hi.1
    · exact hi.2 j h hj.1
  · apply Set.Subset.antisymm
    · exact Set.iUnion_mono fun _ => Set.inter_subset_left
    · intro x hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.1 hx
      let indices := (Finset.univ : Finset (Fin (Fintype.card I))).filter (fun j => x ∈ D (e.symm j))
      have hs : indices.Nonempty := ⟨e i,by simp [indices,hi]⟩
      let k := indices.min' hs
      let j := e.symm k
      have hj : x ∈ D j := (Finset.mem_filter.mp (Finset.min'_mem indices hs)).2
      refine Set.mem_iUnion.2 ⟨j,hj,?_⟩
      intro i' hi' hx'
      have hMem : e i' ∈ indices := by simp [indices,hx']
      have hLe : k ≤ e i' := Finset.min'_le _ _ hMem
      have hjEq : e j = k := e.apply_symm_apply _
      exact hLe.not_gt (hjEq ▸ hi')

theorem finite_definable_partition_of_cover {I : Type*}
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier V) (BaseAssignments S.carrier V))
    (A : Set (SortedAssignment X V)) (hA : SortedDefinableOver M S.carrier A)
    (B : I → Set (SortedAssignment X V)) (hB : ∀ i, SortedDefinableOver M S.carrier (B i))
    (cover : ∀ x ∈ A, ∃ i, x ∈ B i) :
    ∃ (C : Finset I) (D : {i : I // i ∈ C} → Set (SortedAssignment X V)),
      (∀ i, SortedDefinableOver M S.carrier (D i)) ∧ (∀ i, D i ⊆ B i.val) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧ (⋃ i, D i) = A := by
  obtain ⟨C,hC⟩ := finite_definable_cover sat A hA B hB cover
  let J := {i : I // i ∈ C}
  obtain ⟨D,hD,sub,disj,un⟩ := disjoint_definable_subcover (fun i : J => A ∩ B i.val)
    (fun i => hA.inter (hB i.val))
  refine ⟨C,D,hD,fun i x hx => (sub i hx).2,disj,?_⟩
  rw [un]
  apply Set.Subset.antisymm
  · rintro x hx
    obtain ⟨_,hp⟩ := Set.mem_iUnion.1 hx
    exact hp.1
  · intro x hx
    obtain ⟨i,hi,hix⟩ := hC x hx
    exact Set.mem_iUnion.2 ⟨⟨i,hi⟩,hx,hix⟩

end GeneralizedEuler.Section5
