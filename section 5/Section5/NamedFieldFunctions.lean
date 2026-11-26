module

public import Section5.DefinableRelations
public import Section5.LiftBoundaryDimension

/-! A fixed-base partial field graph can be made total by assigning a
base point on the complement of its domain. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {n : ℕ}

theorem named_field_value_graph (c : S.carrier .vf) :
    DefinableRelation M S.carrier (fun (_ : fieldAssignment n X) (y : fieldAssignment 1 X) =>
      c.val = y .vf 0) := by
  let U := SumVariables (MixedVariables n Empty) (MixedVariables 1 Empty)
  let term : SortedTerm L E (WithBase S.carrier U) .vf := .var (.inl c)
  unfold DefinableRelation
  convert SortedDefinableOver.coordinate_eq_term (M := M) (A := S.carrier) (Var := U)
    .vf (.inr 0) term using 1
  ext a
  exact eq_comm

open scoped Classical in
theorem named_total_field_graph
    (D : Set (X .vf)) (f : X .vf → X .vf) (c : S.carrier .vf)
    (g : DefinableRelation M S.carrier (fun (x y : fieldAssignment 1 X) =>
      x .vf 0 ∈ D ∧ f (x .vf 0) = y .vf 0)) :
    DefinableRelation M S.carrier (fun (x y : fieldAssignment 1 X) =>
      (if x .vf 0 ∈ D then f (x .vf 0) else c.val) = y .vf 0) := by
  classical
  have all : SortedDefinableOver M S.carrier (Set.univ : Set (fieldAssignment 1 X)) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  have domain : SortedDefinableOver M S.carrier {x : fieldAssignment 1 X | x .vf 0 ∈ D} := by
    convert g.preimage all using 1
    ext x
    constructor
    · intro h
      exact ⟨fieldTupleAssignment (fun _ => f (x .vf 0)),Set.mem_univ _,h,rfl⟩
    · rintro ⟨_,_,h,_⟩
      exact h
  apply (g.union ((named_field_value_graph c).inter_left domain.compl)).congr
  intro x y
  by_cases h : x .vf 0 ∈ D <;> simp [h]

end GeneralizedEuler.Section5
