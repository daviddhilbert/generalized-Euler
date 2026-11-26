module

public import Section5.RelativeRVWitnesses
public import Section5.RVObjectLifts

/-! Lift a relative RV graph without adding the retained parameters
to the active coordinates of the object. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P : TCsort → Type} {r k : ℕ}

local notation "U" => RVVariables (Fin r)
local notation "V" => RVVariables (Fin k)
local notation "W" => MixedVariables k (Fin r)

@[expose] def relativeRVLift (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))) :
    Set (SortedAssignment X (SumVariables P W)) :=
  {x | appendAssignments
    (appendAssignments (fun s => x s ∘ Sum.inl) (rvTupleAssignment (x .rv ∘ Sum.inr)))
    (rvTupleAssignment (M.rvMap ∘ x .vf ∘ Sum.inr)) ∈ G}

theorem relativeRVLift_definable
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (hg : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier (relativeRVLift (M := M) G) := by
  let A := SumVariables (SumVariables P W) V
  let tag (s : TCsort) : SumVariables (SumVariables P U) V s → A s
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => match s with
      | .vf => i.elim
      | .rv => .inl (.inr i)
    | .inr i => .inr i
  let lead (s : TCsort) : SumVariables (MixedVariables k Empty) V s → A s
    | .inl i => match s with
      | .vf => .inl (.inr i)
      | .rv => i.elim
    | .inr i => .inr i
  have hLead := fieldLead_definable (M := M) (S := S) (n := k)
  unfold DefinableRelation at hLead
  have mixed := (hg.pullback_relabel tag).inter (hLead.pullback_relabel lead)
  convert definable_project_mixed mixed using 1
  ext x
  let p : SortedAssignment X P := fun s => x s ∘ Sum.inl
  let u : SortedAssignment X U := rvTupleAssignment (x .rv ∘ Sum.inr)
  let f : fieldAssignment k X := fieldTupleAssignment (x .vf ∘ Sum.inr)
  have left (v : SortedAssignment X V) :
      (fun s => (appendAssignments x v s ∘ tag s)) = appendAssignments (appendAssignments p u) v := by
    funext s i
    rcases i with (i | i) | i
    · rfl
    · cases s
      · exact i.elim
      · rfl
    · rfl
  change appendAssignments (appendAssignments p u) (fieldLead M f) ∈ G ↔
    ∃ v : SortedAssignment X V, (fun s => appendAssignments x v s ∘ tag s) ∈ G ∧
      fieldLead M (fun s => (appendAssignments x v s ∘ lead s) ∘ Sum.inl) =
        (fun s => (appendAssignments x v s ∘ lead s) ∘ Sum.inr)
  simp only [left]
  change appendAssignments (appendAssignments p u) (fieldLead M f) ∈ G ↔
    ∃ v : SortedAssignment X V, appendAssignments (appendAssignments p u) v ∈ G ∧ fieldLead M f = v
  exact ⟨fun h => ⟨_,h,rfl⟩,fun ⟨_,h,rfl⟩ => h⟩

theorem relativeRVLift_finite_fibers
    {D : Set (SortedAssignment X (SumVariables P U))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    {zero : X .rv} {bound : ℕ} {p : SortedAssignment X P}
    (h : RelativeRVWitness D G zero bound p) (x : Fin k → X .vf) :
    {t : Fin r → X .rv | appendAssignments p (fun | .vf => x | .rv => t) ∈ relativeRVLift (M := M) G}.Finite := by
  let v := fieldLead M (fieldTupleAssignment x)
  have fin := h.finite_fiber v
  have inj : Function.Injective (rvTupleAssignment (X := X) (n := r)) :=
    fun _ _ eq => congrFun eq .rv
  apply (fin.preimage inj.injOn).subset
  intro t ht
  change appendAssignments (appendAssignments p (rvTupleAssignment t)) v ∈ G
  exact ht

end GeneralizedEuler.Section5
