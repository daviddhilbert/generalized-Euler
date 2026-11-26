module

public import Section5.ProjectedFieldChoice

/-! Separate the retained field tuple from its omitted leading-term fibers. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {n k : ℕ} {U : Set (labelAssignment n X)}

/-- The natural coordinate projection on the field pullback. -/
@[expose] def projectFieldLift (p : Fin k → Fin n) (a : fieldLiftDomain M U) :
    fieldLiftDomain M (projectLabels p '' U) :=
  ⟨projectFields p a.val,by
    change fieldLead M (projectFields p a.val) ∈ projectLabels p '' U
    rw [projectFields_fieldLead]
    exact Set.mem_image_of_mem _ a.property⟩

/-- The omitted coordinates in the original coordinate order. -/
abbrev Omitted (p : Fin k ↪ Fin n) := ((Set.range p)ᶜ : Set (Fin n))

theorem fieldAssignment_ext {a b : fieldAssignment n X}
    (h : ∀ j, a .vf j = b .vf j) : a = b := by
  funext s i
  cases s with
  | vf => exact h i
  | rv => exact i.elim

variable (p : Fin k ↪ Fin n)
  (rep : fieldLiftDomain M (projectLabels p '' U) → fieldLiftDomain M U)

abbrev omittedFieldFiber (a : fieldLiftDomain M (projectLabels p '' U)) :=
  {z : Omitted p → X .vf // ∀ j, M.rvMap (z j) = M.rvMap ((rep a).val .vf j.val)}

variable (choiceProjection : ∀ a, projectFields p (rep a).val = a.val)
  (inj : Set.InjOn (projectLabels p) U)

include choiceProjection inj in
private theorem omittedLabel_eq {a : fieldLiftDomain M (projectLabels p '' U)}
    (b : (projectFieldLift (M := M) p ⁻¹' {a} : Set (fieldLiftDomain M U))) :
    fieldLead M b.val.val = fieldLead M (rep a).val := by
  have he : projectFieldLift p b.val = a := b.property
  have pro : projectFields p b.val.val = a.val := congrArg Subtype.val he
  exact label_eq_of_projected_labels p inj b.val (rep a)
    (congrArg (fieldLead M) (pro.trans (choiceProjection a).symm))

include choiceProjection in
private theorem lead_merge_eq {a : fieldLiftDomain M (projectLabels p '' U)}
    (z : omittedFieldFiber p rep a) :
    fieldLead M (fieldTupleAssignment (mergeCoordinates p (a.val .vf) z.val)) =
      fieldLead M (rep a).val := by
  funext s j
  cases s with
  | vf => exact j.elim
  | rv =>
    change M.rvMap (mergeCoordinates p (a.val .vf) z.val j) = M.rvMap ((rep a).val .vf j)
    by_cases h : j ∈ Set.range p
    · obtain ⟨i,rfl⟩ := h
      rw [mergeCoordinates_selected]
      exact congrArg M.rvMap (congrFun (congrFun (choiceProjection a) .vf) i).symm
    · rw [show mergeCoordinates p (a.val .vf) z.val j = z.val ⟨j,h⟩ from
          mergeCoordinates_omitted p _ _ ⟨j,h⟩]
      exact z.property ⟨j,h⟩

/-- Over a fixed retained field tuple, the lift of an injectively projected
set is exactly the product of the remaining leading-term fibers. -/
def omittedFieldFiberEquiv (a : fieldLiftDomain M (projectLabels p '' U)) :
    (projectFieldLift (M := M) p ⁻¹' {a} : Set (fieldLiftDomain M U)) ≃
      omittedFieldFiber p rep a where
  toFun b := ⟨fun j => b.val.val .vf j.val,fun j =>
    congrFun (congrFun (omittedLabel_eq p rep choiceProjection inj b) .rv) j.val⟩
  invFun z := by
    let t := fieldTupleAssignment (mergeCoordinates p (a.val .vf) z.val)
    have hu : fieldLead M t ∈ U := by
      rw [show fieldLead M t = fieldLead M (rep a).val from lead_merge_eq p rep choiceProjection z]
      exact (rep a).property
    let u : fieldLiftDomain M U := ⟨t,hu⟩
    have he : projectFields p t = a.val :=
      fieldAssignment_ext (mergeCoordinates_selected p _ _)
    exact ⟨u,Subtype.ext he⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    apply fieldAssignment_ext
    intro j
    let z (j : Omitted p) := b.val.val .vf j.val
    change mergeCoordinates p (a.val .vf) z j = b.val.val .vf j
    by_cases h : j ∈ Set.range p
    · obtain ⟨i,rfl⟩ := h
      rw [mergeCoordinates_selected]
      have e : projectFieldLift p b.val = a := b.property
      exact (congrFun (congrFun (congrArg Subtype.val e) .vf) i).symm
    · exact mergeCoordinates_omitted p _ _ ⟨j,h⟩
  right_inv z := by
    apply Subtype.ext
    funext j
    exact mergeCoordinates_omitted p _ _ j

/-- Split the whole field pullback using the product over each retained
tuple. -/
def splitProjectedFieldLift :
    fieldLiftDomain M U ≃
      Σ a : fieldLiftDomain M (projectLabels p '' U), omittedFieldFiber p rep a :=
  (Equiv.sigmaPreimageEquiv (projectFieldLift p)).symm.trans
    (Equiv.sigmaCongrRight (omittedFieldFiberEquiv p rep choiceProjection inj))

theorem splitProjectedFieldLift_retained (x : fieldLiftDomain M U) :
    (splitProjectedFieldLift p rep choiceProjection inj x).1 = projectFieldLift p x := by
  rfl

theorem splitProjectedFieldLift_omitted (x : fieldLiftDomain M U) (j : Omitted p) :
    (splitProjectedFieldLift p rep choiceProjection inj x).2.val j = x.val .vf j.val := by
  rfl

theorem splitProjectedFieldLift_symm_field (a : fieldLiftDomain M (projectLabels p '' U))
    (z : omittedFieldFiber p rep a) (j : Fin n) :
    ((splitProjectedFieldLift p rep choiceProjection inj).symm ⟨a,z⟩).val .vf j =
      mergeCoordinates p (a.val .vf) z.val j := by
  rfl

end GeneralizedEuler.Section5
