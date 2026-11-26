module

public import Section5.DefinableBoundaryLifting

/-! Restrict an RV bijection and identify the relative field lift with
the lift of the corresponding ambient label sets. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {U V : Set (labelAssignment n X)}

variable (e : U ≃ V) (A : Set U)

def restrictedLabelEquiv :
    (Subtype.val '' A : Set (labelAssignment n X)) ≃
      (Subtype.val '' (e '' A) : Set (labelAssignment n X)) :=
  (Equiv.Set.image Subtype.val A Subtype.val_injective).symm.trans
    ((e.image A).trans (Equiv.Set.image Subtype.val (e '' A) Subtype.val_injective))

theorem restrictedLabelEquiv_apply (u : U) (hu : u ∈ A) :
    (restrictedLabelEquiv e A ⟨u.val,⟨u,hu,rfl⟩⟩).val = (e u).val := by
  let P := Equiv.Set.image Subtype.val A Subtype.val_injective
  change (e (P.symm (P ⟨u,hu⟩)).val).val = _
  rw [P.symm_apply_apply]

theorem restrictedLabelEquiv_graph
    (hA : SortedDefinableOver M S.carrier (Subtype.val '' A))
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b)) :
    DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ Subtype.val '' A,
      (restrictedLabelEquiv e A ⟨a,ha⟩).val = b) := by
  apply (hE.inter_left hA).congr
  intro a b
  constructor
  · rintro ⟨⟨ha,he⟩,hA'⟩
    obtain ⟨u,hu,rfl⟩ := hA'
    exact ⟨⟨u,hu,rfl⟩,(restrictedLabelEquiv_apply e A u hu).trans he⟩
  · rintro ⟨⟨u,hu,rfl⟩,he⟩
    exact ⟨⟨u.property,(restrictedLabelEquiv_apply e A u hu).symm.trans he⟩,u,hu,rfl⟩

theorem restrictedLabelEquiv_target_definable
    (hA : SortedDefinableOver M S.carrier (Subtype.val '' A))
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b)) :
    SortedDefinableOver M S.carrier (Subtype.val '' (e '' A)) := by
  have hd := (restrictedLabelEquiv_graph e A hA hE).image hA
  convert hd using 1
  ext b
  constructor
  · intro hb
    obtain ⟨a,ha⟩ := (restrictedLabelEquiv e A).surjective ⟨b,hb⟩
    exact ⟨a.val,a.property,a.property,congrArg Subtype.val ha⟩
  · rintro ⟨a,_,ha,rfl⟩
    exact (restrictedLabelEquiv e A ⟨a,ha⟩).property

/-- The two ways of forming the restriction have identical field tuples. -/
def restrictFieldDomainEquiv :
    ((liftedLabel (M := M) U) ⁻¹' A : Set (fieldLiftDomain M U)) ≃
      fieldLiftDomain M (Subtype.val '' A) where
  toFun x := ⟨x.val.val, ⟨liftedLabel U x.val,x.property,rfl⟩⟩
  invFun x := by
    have hx : fieldLead M x.val ∈ Subtype.val '' A := x.property
    have hu : fieldLead M x.val ∈ U := by
      obtain ⟨a,_,he⟩ := hx
      exact he ▸ a.property
    refine ⟨⟨x.val,hu⟩,?_⟩
    obtain ⟨a,ha,he⟩ := hx
    have eq : a = liftedLabel U ⟨x.val,hu⟩ := Subtype.ext he
    change liftedLabel U ⟨x.val,hu⟩ ∈ A
    exact eq ▸ ha
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transfer a lift of ambient label subsets to the relative domains.
This preserves the already defined field graph. -/
theorem relative_lift_of_restricted
    (has : HasDefinableFieldLift S (restrictedLabelEquiv e A)) :
    ∃ f : ((liftedLabel (M := M) U) ⁻¹' A) ≃ ((liftedLabel (M := M) V) ⁻¹' (e '' A)),
      (∀ x, liftedLabel V (f x).val = e (liftedLabel U x.val)) ∧
      DefinableRelation M S.carrier (fun a b =>
        ∃ ha : a ∈ fieldLiftDomain M U, ∃ hA : liftedLabel U ⟨a,ha⟩ ∈ A,
          (f ⟨⟨a,ha⟩,hA⟩).val.val = b) := by
  obtain ⟨f,hF,fDef⟩ := has
  let P := restrictFieldDomainEquiv (M := M) A
  let Q := restrictFieldDomainEquiv (M := M) (e '' A)
  let F := P.trans (f.trans Q.symm)
  refine ⟨F,?_,?_⟩
  · intro x
    apply Subtype.ext
    have hx := congrArg Subtype.val (hF (P x))
    exact hx.trans (restrictedLabelEquiv_apply e A (liftedLabel U x.val) x.property)
  · apply fDef.congr
    intro a b
    constructor
    · rintro ⟨ha,he⟩
      have hx : fieldLead M a ∈ Subtype.val '' A := ha
      obtain ⟨u,hu,hu'⟩ := hx
      have hU : a ∈ fieldLiftDomain M U := by
        change fieldLead M a ∈ U
        exact hu' ▸ u.property
      have eU : u = liftedLabel U ⟨a,hU⟩ := Subtype.ext hu'
      exact ⟨hU,eU ▸ hu,he⟩
    · rintro ⟨ha,hA',he⟩
      exact ⟨⟨liftedLabel U ⟨a,ha⟩,hA',rfl⟩,he⟩

end GeneralizedEuler.Section5
