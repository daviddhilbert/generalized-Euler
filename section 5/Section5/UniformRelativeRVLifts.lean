module

public import Section5.RelativeRVLifts
public import Section5.GeneratedParameterSchemes

/-! Choose relative lift presentations with different arities and
degrees on a finite definable partition of the retained parameters. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P U : TCsort → Type}

structure RelativeRVLiftScheme (M : SortedStructure L E X) (S : SortedSubstructure M)
    (P U : TCsort → Type) where
  arity : ℕ
  degree : ℕ
  bound : ℕ
  tags : Set (SortedAssignment X (SumVariables P (RVVariables (Fin arity))))
  labelGraph : Set (SortedAssignment X
    (SumVariables (SumVariables P (RVVariables (Fin arity))) (RVVariables (Fin degree))))
  liftGraph : Set (SortedAssignment X
    (SumVariables (SumVariables P U) (MixedVariables degree (Fin arity))))
  tagsDefinable : SortedDefinableOver M S.carrier tags
  labelDefinable : SortedDefinableOver M S.carrier labelGraph
  liftGraphDefinable : SortedDefinableOver M S.carrier liftGraph

namespace RelativeRVLiftScheme

variable (A : Set (SortedAssignment X (SumVariables P U)))
  (i : RelativeRVLiftScheme M S P U) (zero : S.carrier .rv)

@[expose] def valid (p : SortedAssignment X P) : Prop :=
  RelativeRVWitness i.tags i.labelGraph zero.val i.bound p ∧
    FiberBijectionScheme A (relativeRVLift (M := M) i.labelGraph) i.liftGraph p

theorem valid_definable [Finite (U .vf)] [Finite (U .rv)] (ha : SortedDefinableOver M S.carrier A) :
    SortedDefinableOver M S.carrier {p | i.valid A zero p} :=
  (relativeRVWitness_definable i.tagsDefinable i.labelDefinable zero i.bound).inter
    (fiberBijectionScheme_definable ha (relativeRVLift_definable i.labelDefinable) i.liftGraphDefinable)

end RelativeRVLiftScheme

theorem uniform_relative_rv_lifts [Finite (U .vf)] [Finite (U .rv)]
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (zero : S.carrier .rv)
    (D : Set (SortedAssignment X P)) (hD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U))) (ha : SortedDefinableOver M S.carrier A)
    (cover : ∀ p ∈ D, ∃ i : RelativeRVLiftScheme M S P U, i.valid A zero p) :
    ∃ (C : Finset (RelativeRVLiftScheme M S P U)) (pieces : {i // i ∈ C} → Set (SortedAssignment X P)),
      (∀ i, SortedDefinableOver M S.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid A zero p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D :=
  finite_definable_partition_of_cover sat D hD (fun i : RelativeRVLiftScheme M S P U => {p | i.valid A zero p})
    (fun i => i.valid_definable A zero ha) cover

end GeneralizedEuler.Section5
