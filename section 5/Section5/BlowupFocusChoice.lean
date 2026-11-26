module

public import Section5.ProjectedFieldSplitting

/-! A definable focus for a blowup uses the retained field tuple.
The projection of the RV labels is assumed injective on the piece. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n k : ℕ} {U : Set (labelAssignment n X)}

/-- Choose the representative of the omitted label over the remaining
field variables and keep the same base for its graph. -/
theorem definable_blowup_focus (p : Fin k ↪ Fin n) (j : Fin n)
    (inj : Set.InjOn (projectLabels p) U)
    (surj : Function.Surjective M.rvMap)
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (MixedVariables k Empty))
      (BaseAssignments S.carrier (MixedVariables k Empty)))
    (elem : ∀ a : fieldAssignment k X, let B := M.termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize M (fun s i => (v s i).val))
    (hU : SortedDefinableOver M S.carrier U) :
    let D := fieldLiftDomain M (projectLabels p '' U)
    ∃ c : D → X .vf,
      (∀ x : fieldLiftDomain M U, M.rvMap (c (projectFieldLift p x)) = M.rvMap (x.val .vf j)) ∧
      DefinableRelation M S.carrier (fun a (b : fieldAssignment 1 X) =>
        ∃ ha : a ∈ D, c ⟨a,ha⟩ = b .vf 0) := by
  intro D
  obtain ⟨rep,hRep,repDef⟩ := definable_projected_field_completion p surj sat elem hU
  let c (a : D) := (rep a).val .vf j
  refine ⟨c,?_,?_⟩
  · intro x
    have he : fieldLead M (rep (projectFieldLift p x)).val = fieldLead M x.val :=
      label_eq_of_projected_labels p inj _ _ (congrArg (fieldLead M) (hRep (projectFieldLift p x)))
    exact congrFun (congrFun he .rv) j
  · let q : Fin 1 → Fin n := fun _ => j
    apply (repDef.comp (projectFields_definable q)).congr
    intro a b
    constructor
    · rintro ⟨_,⟨ha,rfl⟩,he⟩
      exact ⟨ha,congrFun (congrFun he .vf) 0⟩
    · rintro ⟨ha,he⟩
      refine ⟨(rep ⟨a,ha⟩).val,⟨ha,rfl⟩,?_⟩
      apply fieldAssignment_ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact he

end GeneralizedEuler.Section5
