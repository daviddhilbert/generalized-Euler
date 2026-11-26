module

public import Section5.DefinableFiberBounds

/-! Validity of a relative RV object is first order once its arity,
degree and fiber bound are fixed. Parameter variables stay in place
when the label and tag variables are interchanged. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P : TCsort → Type} {r k : ℕ}

local notation "U" => RVVariables (Fin r)
local notation "V" => RVVariables (Fin k)

@[expose] def RelativeRVWitness
    (D : Set (SortedAssignment X (SumVariables P U)))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (zero : X .rv) (bound : ℕ) (p : SortedAssignment X P) : Prop :=
  (∀ u, appendAssignments p u ∈ D ↔ ∃ v, appendAssignments (appendAssignments p u) v ∈ G) ∧
  (∀ u v w, appendAssignments (appendAssignments p u) v ∈ G →
    appendAssignments (appendAssignments p u) w ∈ G → v = w) ∧
  (∀ u v, appendAssignments (appendAssignments p u) v ∈ G → ∀ j, v .rv j ≠ zero) ∧
  (∀ (v : SortedAssignment X V) (a : Fin (bound+1) → SortedAssignment X U),
    (∀ i, appendAssignments (appendAssignments p (a i)) v ∈ G) → ¬ Function.Injective a)

theorem relativeRVWitness_definable
    {D : Set (SortedAssignment X (SumVariables P U))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (hd : SortedDefinableOver M S.carrier D) (hg : SortedDefinableOver M S.carrier G)
    (zero : S.carrier .rv) (bound : ℕ) :
    SortedDefinableOver M S.carrier {p | RelativeRVWitness D G zero.val bound p} := by
  let W := SumVariables (SumVariables P U) V
  let W' := SumVariables (SumVariables P V) U
  let swap (s : TCsort) : W s → W' s
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr i
    | .inr i => .inl (.inr i)
  let H : Set (SortedAssignment X W') := {x | (fun s => x s ∘ swap s) ∈ G}
  have hH : SortedDefinableOver M S.carrier H := hg.pullback_relabel swap
  have boundDef := definable_forall_assignments (fiberCardBound_definable hH bound)
  have nzero := SortedDefinableOver.iInter (fun j : Fin k =>
    (SortedDefinableOver.coordinate_eq_parameter (M := M) (A := S.carrier) (Var := W)
      .rv (.inr j) zero).compl)
  have nonzero := definable_forall_assignments (definable_forall_assignments (hg.compl.union nzero))
  have dom := definable_forall_iff_exists D G hd hg
  have unique := definable_fiberwise_functional G hg
  convert dom.inter (unique.inter (nonzero.inter boundDef)) using 1
  ext p
  simp only [RelativeRVWitness,FiberCardBound,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_union,
    Set.mem_compl_iff,Set.mem_iInter]
  have hswap (u : SortedAssignment X U) (v : SortedAssignment X V) :
      appendAssignments (appendAssignments p v) u ∈ H ↔ appendAssignments (appendAssignments p u) v ∈ G := by
    change (fun s => (appendAssignments (appendAssignments p v) u) s ∘ swap s) ∈ G ↔ _
    have eq : (fun s => (appendAssignments (appendAssignments p v) u) s ∘ swap s) =
        appendAssignments (appendAssignments p u) v := by
      funext s i
      rcases i with (i | i) | i <;> rfl
    rw [eq]
  simp only [hswap]
  classical
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_left
  intro _
  refine forall_congr' fun u => forall_congr' fun v => ?_
  constructor
  · intro h
    by_cases hg' : appendAssignments (appendAssignments p u) v ∈ G
    · exact Or.inr (h hg')
    · exact Or.inl hg'
  · intro h hg'
    exact h.elim (fun hn => False.elim (hn hg')) id

theorem RelativeRVWitness.finite_fiber
    {D : Set (SortedAssignment X (SumVariables P U))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    {zero : X .rv} {bound : ℕ} {p : SortedAssignment X P}
    (h : RelativeRVWitness D G zero bound p) (v : SortedAssignment X V) :
    {u | appendAssignments (appendAssignments p u) v ∈ G}.Finite := by
  by_contra inf
  have hi : {u | appendAssignments (appendAssignments p u) v ∈ G}.Infinite := inf
  let f := hi.natEmbedding
  let a (i : Fin (bound+1)) := (f i.val).val
  exact h.2.2.2 v a (fun i => (f i.val).property)
    (fun _ _ eq => Fin.ext (f.injective (Subtype.ext eq)))

end GeneralizedEuler.Section5
