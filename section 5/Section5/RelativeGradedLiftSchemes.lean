module

public import Section5.RelativeRVLiftChoice

/-! A graded lift scheme is a finite partition of the input fiber
with one relative RV object in a fixed degree on each part. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P U : TCsort → Type}

structure RelativeGradedLiftScheme (M : SortedStructure L E X) (S : SortedSubstructure M)
    (P U : TCsort → Type) where
  count : ℕ
  source : Fin count → Set (SortedAssignment X (SumVariables P U))
  sourceDefinable : ∀ i, SortedDefinableOver M S.carrier (source i)
  object : Fin count → RelativeRVLiftScheme M S P U

namespace RelativeGradedLiftScheme

variable (W : RelativeGradedLiftScheme M S P U) (zero : S.carrier .rv)
  (A : Set (SortedAssignment X (SumVariables P U)))

@[expose] def valid (p : SortedAssignment X P) : Prop :=
  (∀ u, appendAssignments p u ∈ A ↔ ∃ i, appendAssignments p u ∈ W.source i) ∧
  (∀ i j, i ≠ j → ∀ u, ¬ (appendAssignments p u ∈ W.source i ∧ appendAssignments p u ∈ W.source j)) ∧
  ∀ i, (W.object i).valid (W.source i) zero p

theorem valid_definable [Finite (U .vf)] [Finite (U .rv)] (defA : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier {p | W.valid zero A p} := by
  let D := ⋃ i, W.source i
  have hd : SortedDefinableOver M S.carrier D := SortedDefinableOver.iUnion W.sourceDefinable
  have cov := definable_forall_assignments ((defA.inter hd).union (defA.compl.inter hd.compl))
  let distinct := {q : Fin W.count × Fin W.count // q.1 ≠ q.2}
  have disj := SortedDefinableOver.iInter (fun i : distinct => definable_forall_assignments
    ((W.sourceDefinable i.val.1).inter (W.sourceDefinable i.val.2)).compl)
  have localValid := SortedDefinableOver.iInter (fun i => (W.object i).valid_definable (W.source i) zero (W.sourceDefinable i))
  convert cov.inter (disj.inter localValid) using 1
  ext p
  simp only [valid,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_union,Set.mem_compl_iff,D,Set.mem_iUnion]
  constructor
  · rintro ⟨hcov,hdisj,hloc⟩
    refine ⟨?_,fun q u => hdisj q.val.1 q.val.2 q.property u,hloc⟩
    intro u
    classical
    by_cases hu : appendAssignments p u ∈ A
    · exact Or.inl ⟨hu,(hcov u).1 hu⟩
    · exact Or.inr ⟨hu,fun h => hu ((hcov u).2 h)⟩
  · rintro ⟨hcov,hdisj,hloc⟩
    refine ⟨?_,fun i j h u => hdisj ⟨(i,j),h⟩ u,hloc⟩
    intro u
    exact (hcov u).elim (fun h => iff_of_true h.1 h.2) (fun h => iff_of_false h.1 h.2)

end RelativeGradedLiftScheme

theorem uniform_graded_relative_lift_schemes [Finite (U .vf)] [Finite (U .rv)]
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (zero : S.carrier .rv) (D : Set (SortedAssignment X P)) (defD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U))) (defA : SortedDefinableOver M S.carrier A)
    (pointwise : ∀ p ∈ D, ∃ W : RelativeGradedLiftScheme M S P U, W.valid zero A p) :
    ∃ (C : Finset (RelativeGradedLiftScheme M S P U)) (pieces : {i // i ∈ C} → Set (SortedAssignment X P)),
      (∀ i, SortedDefinableOver M S.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid zero A p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D :=
  finite_definable_partition_of_cover sat D defD (fun i : RelativeGradedLiftScheme M S P U => {p | i.valid zero A p})
    (fun i => i.valid_definable zero A defA) pointwise

end GeneralizedEuler.Section5
