module

public import Section5.DefinableLiftLabels

/-! Choose the two VF maps in the full-arity lifting step over the original base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ}

variable (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (MixedVariables n Empty))
  (BaseAssignments S.carrier (MixedVariables n Empty)))
  (elem : ∀ x : fieldAssignment n X, let B := M.termGenerated (namedFieldAssignment S x)
    ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
      φ.realize B.structureOn v ↔ φ.realize M (fun s i => (v s i).val))

include sat elem in
/-- Choose a field tuple above the prescribed target label, uniformly over the
source field tuples. -/
theorem definable_candidate_lift {U V : Set (labelAssignment n X)}
    (e : U ≃ V) (hU : SortedDefinableOver M S.carrier U)
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b))
    (surj : Function.Surjective M.rvMap) :
    ∃ h : (fieldLead M ⁻¹' U) → fieldAssignment n X,
      (∀ x, fieldLead M (h x) = (e ⟨fieldLead M x.val,x.property⟩).val) ∧
      DefinableRelation M S.carrier
        (fun x y => ∃ hx : x ∈ fieldLead M ⁻¹' U, h ⟨x,hx⟩ = y) := by
  have hl := fieldLead_definable (M := M) (S := S) (n := n)
  let R (x y : fieldAssignment n X) :=
    ∃ hx : fieldLead M x ∈ U, (e ⟨fieldLead M x,hx⟩).val = fieldLead M y
  have hR : DefinableRelation M S.carrier R :=
    ((hl.comp hE).comp hl.transpose).congr (by
      intro x y
      constructor
      · rintro ⟨_,⟨_,rfl,hx,he⟩,rfl⟩
        exact ⟨hx,he⟩
      · rintro ⟨hx,he⟩
        exact ⟨fieldLead M y,⟨fieldLead M x,rfl,hx,he⟩,rfl⟩)
  obtain ⟨h, hlabel, hdef⟩ := definable_field_choice_of_elementary sat _
    (definable_fieldLead_preimage hU) hR (fun x _ => elem x) (by
      intro x hx
      obtain ⟨y,hy⟩ := fieldLead_surjective surj (e ⟨fieldLead M x,hx⟩).val
      exact ⟨y,hx,hy.symm⟩)
  exact ⟨h,fun x => (hlabel x).choose_spec.symm,hdef⟩

/-- A candidate hits every point of the paired target fibers outside its
ambient RV boundary. The source set is used only through that coverage. -/
theorem image_covers_off_boundary {U V : Set (labelAssignment n X)}
    (e : U ≃ V) (surj : Function.Surjective M.rvMap)
    (h : (fieldLead M ⁻¹' U) → fieldAssignment n X)
    (hlabel : ∀ x, fieldLead M (h x) = (e ⟨fieldLead M x.val,x.property⟩).val)
    {y : fieldAssignment n X} (hy : fieldLead M y ∈ V)
    (off : fieldLead M y ∉ rvBoundary (fieldLead M) (Set.range h)) :
    y ∈ Set.range h := by
  classical
  by_contra hn
  let a := e.symm ⟨fieldLead M y,hy⟩
  obtain ⟨x,hx⟩ := fieldLead_surjective surj a.val
  let x' : fieldLead M ⁻¹' U := ⟨x,by change fieldLead M x ∈ U; rw [hx]; exact a.property⟩
  have he : (⟨fieldLead M x',x'.property⟩ : U) = a := Subtype.ext hx
  apply off
  refine ⟨⟨h x',Set.mem_range_self _,?_⟩, y, rfl, hn⟩
  rw [hlabel,he,e.apply_symm_apply]

theorem definable_range_of_field_graph {D : Set (fieldAssignment n X)}
    (hD : SortedDefinableOver M S.carrier D) (f : D → fieldAssignment n X)
    (hF : DefinableRelation M S.carrier (fun x y => ∃ hx : x ∈ D, f ⟨x,hx⟩ = y)) :
    SortedDefinableOver M S.carrier (Set.range f) := by
  have hd := hF.image hD
  convert hd using 1
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,x.property,rfl⟩
  · rintro ⟨x,_,hx,he⟩
    exact ⟨⟨x,hx⟩,he⟩

include sat elem in
/-- The graph of the candidate and a field choice give a definable right
inverse on the entire good target region. -/
theorem definable_right_inverse_off_boundary {U V : Set (labelAssignment n X)}
    (e : U ≃ V) (hU : SortedDefinableOver M S.carrier U)
    (hV : SortedDefinableOver M S.carrier V)
    (surj : Function.Surjective M.rvMap)
    (h : (fieldLead M ⁻¹' U) → fieldAssignment n X)
    (hlabel : ∀ x, fieldLead M (h x) = (e ⟨fieldLead M x.val,x.property⟩).val)
    (hdef : DefinableRelation M S.carrier
      (fun x y => ∃ hx : x ∈ fieldLead M ⁻¹' U, h ⟨x,hx⟩ = y)) :
    let good := V ∩ (rvBoundary (fieldLead M) (Set.range h))ᶜ
    ∃ g : (fieldLead M ⁻¹' good) → (fieldLead M ⁻¹' U),
      (∀ y, h (g y) = y.val) ∧
      DefinableRelation M S.carrier
        (fun y x => ∃ hy : y ∈ fieldLead M ⁻¹' good, (g ⟨y,hy⟩).val = x) := by
  intro good
  have hrange := definable_range_of_field_graph (definable_fieldLead_preimage hU) h hdef
  have hgood : SortedDefinableOver M S.carrier good :=
    hV.inter (definable_fieldLead_boundary hrange).compl
  obtain ⟨g,hg,hgdef⟩ := definable_field_choice_of_elementary sat _
    (definable_fieldLead_preimage hgood) hdef.transpose (fun x _ => elem x) (by
      intro y hy
      obtain ⟨x,hx⟩ := image_covers_off_boundary e surj h hlabel hy.1 hy.2
      exact ⟨x.val,x.property,hx⟩)
  exact ⟨fun y => ⟨g y,(hg y).choose⟩, fun y => (hg y).choose_spec,hgdef⟩

end GeneralizedEuler.Section5
