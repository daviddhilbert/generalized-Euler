module

public import Section5.ProjectedLiftGraph

/-! Choose field representatives of missing RV coordinates over a
retained field tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n k : ℕ} {U : Set (labelAssignment n X)}

/-- Combine a tuple on selected coordinates with the values on their
complement in the original coordinate order. -/
noncomputable def mergeCoordinates {Y : Type*} (p : Fin k ↪ Fin n) (a : Fin k → Y)
    (z : ((Set.range p)ᶜ : Set (Fin n)) → Y) : Fin n → Y := by
  classical
  exact fun j => if h : j ∈ Set.range p then a h.choose else z ⟨j,h⟩

theorem mergeCoordinates_selected {Y : Type*} (p : Fin k ↪ Fin n) (a : Fin k → Y)
    (z : ((Set.range p)ᶜ : Set (Fin n)) → Y) (i : Fin k) :
    mergeCoordinates p a z (p i) = a i := by
  classical
  have h : p i ∈ Set.range p := Set.mem_range_self i
  rw [mergeCoordinates,dite_eq_left h,p.injective h.choose_spec]

theorem mergeCoordinates_omitted {Y : Type*} (p : Fin k ↪ Fin n) (a : Fin k → Y)
    (z : ((Set.range p)ᶜ : Set (Fin n)) → Y) (j : ((Set.range p)ᶜ : Set (Fin n))) :
    mergeCoordinates p a z j.val = z j := by
  classical
  rw [mergeCoordinates,dite_eq_right j.property]

theorem exists_projected_field_completion (p : Fin k ↪ Fin n)
    (surj : Function.Surjective M.rvMap)
    (a : fieldAssignment k X) (ha : fieldLead M a ∈ projectLabels p '' U) :
    ∃ y : fieldAssignment n X, fieldLead M y ∈ U ∧ projectFields p y = a := by
  classical
  obtain ⟨r,hr,hra⟩ := ha
  obtain ⟨b,hb⟩ := fieldLead_surjective surj r
  let omitted (j : ((Set.range p)ᶜ : Set (Fin n))) := b .vf j.val
  let x := mergeCoordinates p (a .vf) omitted
  have hselected (i : Fin k) : x (p i) = a .vf i :=
    mergeCoordinates_selected p _ _ i
  let y : fieldAssignment n X := fieldTupleAssignment x
  have label : fieldLead M y = r := by
    funext s j
    cases s with
    | vf => exact j.elim
    | rv =>
      change M.rvMap (x j) = r .rv j
      by_cases h : j ∈ Set.range p
      · obtain ⟨i,rfl⟩ := h
        rw [hselected]
        exact (congrFun (congrFun hra .rv) i).symm
      · rw [show x j = b .vf j from mergeCoordinates_omitted p _ _ ⟨j,h⟩]
        exact congrFun (congrFun hb .rv) j
  refine ⟨y,label.symm ▸ hr,?_⟩
  funext s i
  cases s with
  | vf => exact hselected i
  | rv => exact i.elim

/-- Every retained field tuple in the projected lift has a definably
chosen completion to a full field tuple. When the RV projection is
injective, these completions represent the uniquely determined labels. -/
theorem definable_projected_field_completion (p : Fin k ↪ Fin n)
    (surj : Function.Surjective M.rvMap)
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (MixedVariables k Empty))
      (BaseAssignments S.carrier (MixedVariables k Empty)))
    (elem : ∀ a : fieldAssignment k X, let B := M.termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize M (fun s i => (v s i).val))
    (hU : SortedDefinableOver M S.carrier U) :
    let A := fieldLiftDomain M (projectLabels p '' U)
    ∃ rep : A → fieldLiftDomain M U,
      (∀ a, projectFields p (rep a).val = a.val) ∧
      DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ A, (rep ⟨a,ha⟩).val = b) := by
  intro A
  have hA : SortedDefinableOver M S.carrier A :=
    definable_fieldLead_preimage (projectLabels_image_definable p hU)
  have hLift := definable_fieldLead_preimage hU
  have hR := ((projectFields_definable p).inter_left hLift).transpose
  obtain ⟨rep,hRep,hRepDef⟩ := definable_field_choice_of_elementary sat A hA hR
    (fun a _ => elem a) (by
      intro a ha
      obtain ⟨b,hb,hba⟩ := exists_projected_field_completion p surj a ha
      exact ⟨b,hba,hb⟩)
  exact ⟨fun a => ⟨rep a,(hRep a).2⟩,fun a => (hRep a).1,hRepDef⟩

/-- Points with the same projected labels have the same original labels
on an injective projection piece. -/
theorem label_eq_of_projected_labels (p : Fin k → Fin n)
    (inj : Set.InjOn (projectLabels p) U)
    (a b : fieldLiftDomain M U)
    (he : fieldLead M (projectFields p a.val) = fieldLead M (projectFields p b.val)) :
    fieldLead M a.val = fieldLead M b.val := by
  rw [projectFields_fieldLead,projectFields_fieldLead] at he
  exact inj a.property b.property he

end GeneralizedEuler.Section5
