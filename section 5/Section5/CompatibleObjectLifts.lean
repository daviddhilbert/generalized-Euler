module

public import Section5.RVObjectLifts
import all Section2.RVDefinableEquivalence

/-! Lift an RV object isomorphism when its correspondence on structure
labels is a bijection. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.ObjectLift

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}
  (U V : RVObject M S k)

/-- The set of structure labels viewed as sorted assignments. -/
@[expose] def structureLabels (U : RVObject M S k) : Set (labelAssignment k X) :=
  Set.range (rvTupleAssignment ∘ U.label)

@[expose] def structureLabel (U : RVObject M S k) (a : U.carrier) : structureLabels U :=
  ⟨rvTupleAssignment (U.label a),Set.mem_range_self a⟩

theorem structureLabels_definable :
    SortedDefinableOver M S.carrier (structureLabels U) := by
  have h := definable_range_of_rvGraph U.label U.graph
  convert h using 1
  ext a
  change (∃ u : U.carrier, rvTupleAssignment (U.label u) = a) ↔ ∃ u : U.carrier, U.label u = a .rv
  refine ⟨fun ⟨u,he⟩ => ⟨u,congrFun he .rv⟩,fun ⟨u,he⟩ => ⟨u,?_⟩⟩
  funext s i
  cases s with
  | vf => exact i.elim
  | rv => exact congrFun he i

theorem fieldLead_tag (x : carrier U) :
    fieldLead M (fieldTupleAssignment (x.val .vf)) =
      (structureLabel U (tag U x)).val := by
  funext s i
  cases s with
  | vf => exact i.elim
  | rv => exact (congrFun (tag_label U x) i).symm

@[expose] def fieldPoint (x : carrier U) : fieldLiftDomain M (structureLabels U) :=
  ⟨fieldTupleAssignment (x.val .vf),by
    change fieldLead M (fieldTupleAssignment (x.val .vf)) ∈ structureLabels U
    rw [fieldLead_tag U x]
    exact (structureLabel U (tag U x)).property⟩

theorem fieldPoint_label (x : carrier U) :
    liftedLabel (structureLabels U) (fieldPoint U x) = structureLabel U (tag U x) :=
  Subtype.ext (fieldLead_tag U x)

private def mapOfCompatible
    (e : U.carrier → V.carrier)
    (f : fieldLiftDomain M (structureLabels U) → fieldLiftDomain M (structureLabels V))
    (compat : ∀ x : carrier U, liftedLabel (structureLabels V) (f (fieldPoint U x)) =
      structureLabel V (e (tag U x))) (x : carrier U) : carrier V :=
  assemble V (e (tag U x)) ((f (fieldPoint U x)).val .vf) (congrFun (congrArg Subtype.val (compat x)) .rv).symm

private theorem mapOfCompatible_tag
    (e : U.carrier → V.carrier)
    (f : fieldLiftDomain M (structureLabels U) → fieldLiftDomain M (structureLabels V))
    (compat : ∀ x : carrier U, liftedLabel (structureLabels V) (f (fieldPoint U x)) =
      structureLabel V (e (tag U x))) (x : carrier U) :
    tag V (mapOfCompatible U V e f compat x) = e (tag U x) :=
  assemble_tag V _ _ _

private theorem mapOfCompatible_field
    (e : U.carrier → V.carrier)
    (f : fieldLiftDomain M (structureLabels U) → fieldLiftDomain M (structureLabels V))
    (compat : ∀ x : carrier U, liftedLabel (structureLabels V) (f (fieldPoint U x)) =
      structureLabel V (e (tag U x))) (x : carrier U) :
    fieldPoint V (mapOfCompatible U V e f compat x) = f (fieldPoint U x) :=
  Subtype.ext (fieldAssignment_ext (fun _ => rfl))

@[expose] def HasDefinableObjectLift (e : U.carrier ≃ V.carrier) : Prop :=
  ∃ f : carrier U ≃ carrier V, (∀ x, tag V (f x) = e (tag U x)) ∧
    DefinableRelation M S.carrier (fun x y => ∃ hx : x ∈ carrier U, (f ⟨x,hx⟩).val = y)

/-- The chosen lift on the structure labels determines the field map,
while the given object isomorphism determines the RV part. -/
theorem definable_lift_of_compatible_labels
    (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun u => (e u).val)))
    (g : structureLabels U ≃ structureLabels V)
    (he : ∀ u, g (structureLabel U u) = structureLabel V (e u))
    (hLift : HasDefinableFieldLift S g) :
    HasDefinableObjectLift U V e := by
  obtain ⟨f,hF,fDef⟩ := hLift
  have forward (x : carrier U) :
      liftedLabel (structureLabels V) (f (fieldPoint U x)) = structureLabel V (e (tag U x)) := by
    rw [hF,fieldPoint_label,he]
  have backward (x : carrier V) :
      liftedLabel (structureLabels U) (f.symm (fieldPoint V x)) = structureLabel U (e.symm (tag V x)) := by
    apply g.injective
    rw [he,e.apply_symm_apply,← hF,f.apply_symm_apply,fieldPoint_label]
  let fwd := mapOfCompatible U V e f forward
  let bwd := mapOfCompatible V U e.symm f.symm backward
  have fwdTag (x) : tag V (fwd x) = e (tag U x) := mapOfCompatible_tag U V e f forward x
  have bwdTag (y) : tag U (bwd y) = e.symm (tag V y) := mapOfCompatible_tag V U e.symm f.symm backward y
  have fwdField (x) : fieldPoint V (fwd x) = f (fieldPoint U x) := mapOfCompatible_field U V e f forward x
  have bwdField (y) : fieldPoint U (bwd y) = f.symm (fieldPoint V y) :=
    mapOfCompatible_field V U e.symm f.symm backward y
  let F : carrier U ≃ carrier V := ⟨fwd,bwd,by
    intro x
    apply ext
    · have hh : fieldPoint U (bwd (fwd x)) = fieldPoint U x := by
        rw [bwdField,fwdField,f.symm_apply_apply]
      exact congrFun (congrArg Subtype.val hh) .vf
    · rw [bwdTag,fwdTag,e.symm_apply_apply], by
    intro y
    apply ext
    · have hh : fieldPoint V (fwd (bwd y)) = fieldPoint V y := by
        rw [fwdField,bwdField,f.apply_symm_apply]
      exact congrFun (congrArg Subtype.val hh) .vf
    · rw [fwdTag,bwdTag,e.apply_symm_apply]⟩
  refine ⟨F,fwdTag,?_⟩
  let W := SumVariables (Vars U) (Vars V)
  let renameTag : ∀ s, RVVariables (Fin U.arity ⊕ Fin V.arity) s → W s
    | .vf => PEmpty.elim
    | .rv => id
  let renameField : ∀ s, SumVariables (MixedVariables k Empty) (MixedVariables k Empty) s → W s
    | .vf => id
    | .rv => Sum.elim Empty.elim Empty.elim
  unfold DefinableRelation at fDef ⊢
  have both := ((definable U).pullback_relabel (fun _ => Sum.inl)).inter
    ((eDef.pullback_relabel renameTag).inter (fDef.pullback_relabel renameField))
  convert both using 1
  ext w
  let x : SortedAssignment X (Vars U) := fun s => w s ∘ Sum.inl
  let y : SortedAssignment X (Vars V) := fun s => w s ∘ Sum.inr
  let px : fieldAssignment k X := fun s => (w s ∘ renameField s) ∘ Sum.inl
  let py : fieldAssignment k X := fun s => (w s ∘ renameField s) ∘ Sum.inr
  have eX : px = fieldTupleAssignment (x .vf) := fieldAssignment_ext (fun _ => rfl)
  have eY : py = fieldTupleAssignment (y .vf) := fieldAssignment_ext (fun _ => rfl)
  change (∃ hx : x ∈ carrier U, (F ⟨x,hx⟩).val = y) ↔
    x ∈ carrier U ∧ (∃ a : U.carrier, a.val = x .rv ∧ (e a).val = y .rv) ∧
      (∃ hx : px ∈ fieldLiftDomain M (structureLabels U), (f ⟨px,hx⟩).val = py)
  simp only [eX,eY]
  constructor
  · rintro ⟨hx,hy⟩
    let u : carrier U := ⟨x,hx⟩
    change (fwd u).val = y at hy
    have hvf := congrArg (fun b : SortedAssignment X (Vars V) => fieldTupleAssignment (b .vf)) hy
    exact ⟨hx,⟨tag U u,tag_val U u,by
      rw [← fwdTag u]
      exact (tag_val V (fwd u)).trans (congrFun hy .rv)⟩,
      (fieldPoint U u).property, (congrArg Subtype.val (fwdField u)).symm.trans hvf⟩
  · rintro ⟨hx,⟨a,ha,he⟩,hf,hf'⟩
    let u : carrier U := ⟨x,hx⟩
    have htag : tag U u = a := tag_of_val_eq U u a ha
    refine ⟨hx,?_⟩
    funext s i
    cases s with
    | vf =>
      exact congrFun (congrFun ((congrArg Subtype.val (fwdField u)).trans hf') .vf) i
    | rv =>
      have ht : tag V (fwd u) = e a := (fwdTag u).trans (congrArg e htag)
      exact congrFun ((tag_val V (fwd u)).symm.trans ((congrArg Subtype.val ht).trans he)) i

end GeneralizedEuler.Section5.ObjectLift
