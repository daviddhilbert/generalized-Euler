module

public import Section5.RelativeSchemeDescent

/-! A finite list of definable cuts covers a fiber disjointly on a
definable locus of parameters. The same test descends with the cuts. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P Q U : TCsort → Type} {I : Type}

@[expose] def FiberPartitionScheme
    (A : Set (SortedAssignment X (SumVariables P U)))
    (C : I → Set (SortedAssignment X (SumVariables P U))) (p : SortedAssignment X P) : Prop :=
  (∀ u, appendAssignments p u ∈ A ↔ ∃ i, appendAssignments p u ∈ C i) ∧
  (∀ i j, i ≠ j → ∀ u, ¬ (appendAssignments p u ∈ C i ∧ appendAssignments p u ∈ C j))

theorem fiberPartitionScheme_definable [Finite I] [Finite (U .vf)] [Finite (U .rv)]
    {A : Set (SortedAssignment X (SumVariables P U))}
    {C : I → Set (SortedAssignment X (SumVariables P U))}
    (defA : SortedDefinableOver M S.carrier A) (defC : ∀ i, SortedDefinableOver M S.carrier (C i)) :
    SortedDefinableOver M S.carrier {p | FiberPartitionScheme A C p} := by
  have union := SortedDefinableOver.iUnion defC
  have cover := definable_forall_assignments ((defA.inter union).union (defA.compl.inter union.compl))
  let pairs := {ij : I × I // ij.1 ≠ ij.2}
  have disj := SortedDefinableOver.iInter (fun ij : pairs => definable_forall_assignments
    ((defC ij.val.1).inter (defC ij.val.2)).compl)
  convert cover.inter disj using 1
  ext p
  symm
  simp only [FiberPartitionScheme,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_union,Set.mem_compl_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨hc,hd⟩
    exact ⟨fun u => (hc u).elim (fun h => iff_of_true h.1 h.2) (fun h => iff_of_false h.1 h.2),
      fun i j h u => hd ⟨(i,j),h⟩ u⟩
  · rintro ⟨hc,hd⟩
    refine ⟨?_,fun ij u => hd ij.val.1 ij.val.2 ij.property u⟩
    intro u
    classical
    by_cases h : appendAssignments p u ∈ A
    · exact Or.inl ⟨h,(hc u).1 h⟩
    · exact Or.inr ⟨h,fun u' => h ((hc u).2 u')⟩

theorem FiberPartitionScheme.descend
    {A : Set (SortedAssignment X (SumVariables P U))}
    {C : I → Set (SortedAssignment X (SumVariables P U))}
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    {p : SortedAssignment X P} {q : SortedAssignment X Q} (hp : H p q)
    (constA : ∀ p', H p' q → ∀ u, appendAssignments p u ∈ A ↔ appendAssignments p' u ∈ A)
    (constC : ∀ i p', H p' q → ∀ u, appendAssignments p u ∈ C i ↔ appendAssignments p' u ∈ C i)
    (valid : FiberPartitionScheme A C p) :
    FiberPartitionScheme (descendFiberScheme H A) (fun i => descendFiberScheme H (C i)) q := by
  simpa only [FiberPartitionScheme,descendFiberScheme_at hp constA,descendFiberScheme_at hp (constC _)] using valid

end GeneralizedEuler.Section5
