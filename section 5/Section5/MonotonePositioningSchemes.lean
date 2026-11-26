module

public import Section5.PositioningBranchSchemes
public import Section3.Monotonicity

/-! A fixed-base monotone partition supplies the local branch
witnesses for a uniform positioning family. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}
  [LinearOrder (X .vf)]

local notation "U" => MixedVariables 1 Empty
local notation "Avars" => SumVariables P U
local notation "Gvars" => SumVariables (SumVariables P U) U

theorem positioning_scheme_of_monotone_partition
    (p : SortedAssignment X P) {n : ℕ}
    (A : Set (SortedAssignment X Avars)) (G : Set (SortedAssignment X Gvars))
    (f : X .vf → X .vf) (C : Fin n → Set (X .vf))
    (defC : ∀ i, SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier
      {a : SortedAssignment X U | a .vf 0 ∈ C i})
    (cover : ∀ a : SortedAssignment X U, appendAssignments p a ∈ A ↔ ∃ i, a .vf 0 ∈ C i)
    (disjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (part : ∀ i, MonotonePiece f (C i))
    (eval : ∀ a b, appendAssignments (appendAssignments p a) b ∈ G → b .vf 0 = f (a .vf 0)) :
    ∃ W : PositioningBranchScheme M S P, W.valid A G p := by
  apply positioning_branch_scheme_of_generated_partition p A G
    (fun i => {a : SortedAssignment X U | a .vf 0 ∈ C i}) defC cover
  · intro i j ne
    exact Set.disjoint_left.2 (fun _ hi hj => Set.disjoint_left.1 (disjoint ne) hi hj)
  · intro i
    have exactTuple {a b : SortedAssignment X U} (e : a .vf 0 = b .vf 0) : a = b :=
      fieldAssignment_ext (fun j => by rw [Subsingleton.elim j (0 : Fin 1)]; exact e)
    have injects (inj : Set.InjOn f (C i)) (a b c d : SortedAssignment X U)
        (ha : a .vf 0 ∈ C i) (hc : c .vf 0 ∈ C i)
        (hg : appendAssignments (appendAssignments p a) b ∈ G)
        (hh : appendAssignments (appendAssignments p c) d ∈ G) (e : b = d) : a = c := by
      exact exactTuple (inj ha hc ((eval a b hg).symm.trans ((congrFun (congrFun e .vf) 0).trans (eval c d hh))))
    cases part i with
    | const h =>
      exact Or.inl (fun a b c d ha hc hg hh => exactTuple ((eval a b hg).trans ((h _ ha _ hc).trans (eval c d hh).symm)))
    | increasing h => exact Or.inr (injects h.injOn)
    | decreasing h => exact Or.inr (injects h.injOn)

end GeneralizedEuler.Section5
