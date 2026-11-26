module

public import Section5.FieldLiftChoices
public import Section5.PullbackBoundary

/-! Express the definable VF choices in the relative domains used for gluing. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ}

abbrev fieldLiftDomain (M : SortedStructure L E X) (U : Set (labelAssignment n X)) :
    Set (fieldAssignment n X) := fieldLead M ⁻¹' U

@[expose] def liftedLabel (U : Set (labelAssignment n X)) (x : fieldLiftDomain M U) : U :=
  ⟨fieldLead M x.val,x.property⟩

variable (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (MixedVariables n Empty))
  (BaseAssignments S.carrier (MixedVariables n Empty)))
  (elem : ∀ x : fieldAssignment n X, let B := M.termGenerated (namedFieldAssignment S x)
    ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
      φ.realize B.structureOn v ↔ φ.realize M (fun s i => (v s i).val))

include sat elem in
/-- The relative maps have definable graphs in the ambient VF space.
In particular both relative exceptional sets come from ambient definable
sets to which the RV boundary theorem applies. -/
theorem relative_lift_choices {U V : Set (labelAssignment n X)}
    (e : U ≃ V) (hU : SortedDefinableOver M S.carrier U)
    (hV : SortedDefinableOver M S.carrier V)
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b))
    (surj : Function.Surjective M.rvMap) :
    ∃ (h : fieldLiftDomain M U → fieldLiftDomain M V)
      (g : {b : fieldLiftDomain M V // liftedLabel V b ∉ rvBoundary (liftedLabel V) (Set.range h)} →
        fieldLiftDomain M U),
      (∀ x, liftedLabel V (h x) = e (liftedLabel U x)) ∧ (∀ y, h (g y) = y.val) ∧
      DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ fieldLiftDomain M U, (h ⟨a,ha⟩).val = b) ∧
      SortedDefinableOver M S.carrier (Subtype.val '' Set.range h) ∧
      SortedDefinableOver M S.carrier (Subtype.val '' Set.range g) := by
  obtain ⟨H,hH,hHdef⟩ := definable_candidate_lift sat elem e hU hE surj
  obtain ⟨G,hG,hGdef⟩ := definable_right_inverse_off_boundary sat elem e hU hV surj H hH hHdef
  let h (x : fieldLiftDomain M U) : fieldLiftDomain M V :=
    ⟨H x,by change fieldLead M (H x) ∈ V; rw [hH]; exact (e (liftedLabel U x)).property⟩
  have hRange : Subtype.val '' Set.range h = Set.range H := by
    rw [← Set.range_comp]
    rfl
  have hBoundary := rvBoundary_on_pullback (fieldLead M) V (Set.range h)
  rw [hRange] at hBoundary
  have hOff (y : fieldLiftDomain M V) :
      liftedLabel V y ∉ rvBoundary (liftedLabel V) (Set.range h) ↔
        fieldLead M y.val ∉ rvBoundary (fieldLead M) (Set.range H) := by
    rw [show rvBoundary (liftedLabel V) (Set.range h) =
      Subtype.val ⁻¹' rvBoundary (fieldLead M) (Set.range H) from hBoundary]
    rfl
  let target := fieldLiftDomain M (V ∩ (rvBoundary (fieldLead M) (Set.range H))ᶜ)
  let onAmbient (y : {b : fieldLiftDomain M V //
    liftedLabel V b ∉ rvBoundary (liftedLabel V) (Set.range h)}) : target :=
    ⟨y.val.val, y.val.property, (hOff y.val).1 y.property⟩
  have hOnAmbient : Function.Surjective onAmbient := by
    intro y
    let b : fieldLiftDomain M V := ⟨y.val,y.property.1⟩
    exact ⟨⟨b,(hOff b).2 y.property.2⟩,Subtype.ext rfl⟩
  let g := G ∘ onAmbient
  have hHR := definable_range_of_field_graph (definable_fieldLead_preimage hU) H hHdef
  have hRB := definable_fieldLead_boundary hHR
  have hGR := definable_range_of_field_graph (definable_fieldLead_preimage (hV.inter hRB.compl))
    (Subtype.val ∘ G) hGdef
  have gRange : Subtype.val '' Set.range g = Set.range (Subtype.val ∘ G) := by
    rw [← Set.range_comp]
    exact hOnAmbient.range_comp (Subtype.val ∘ G)
  exact ⟨h,g,fun x => Subtype.ext (hH x),fun y => Subtype.ext (hG (onAmbient y)),hHdef,
    hRange.symm ▸ hHR,gRange.symm ▸ hGR⟩

end GeneralizedEuler.Section5
