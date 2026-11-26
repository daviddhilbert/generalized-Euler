module

public import Section5.CompatibleObjectLifts

/-! Injectively labelled RV objects reduce to their sets of structure labels. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.ObjectLift

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}
  (U V : RVObject M S k)

theorem relation_of_rvGraph {I J : Type} {D : Set (I → X .rv)} {f : D → J → X .rv}
    (h : SortedDefinableOver M S.carrier (rvGraph f)) :
    DefinableRelation M S.carrier
      (fun a : SortedAssignment X (RVVariables I) => fun b : SortedAssignment X (RVVariables J) =>
        ∃ x : D, x.val = a .rv ∧ f x = b .rv) := by
  let r : ∀ s, RVVariables (I ⊕ J) s → SumVariables (RVVariables I) (RVVariables J) s
    | .vf => PEmpty.elim
    | .rv => id
  exact h.pullback_relabel r

private theorem rvAssignment_ext {n : ℕ} {a b : labelAssignment n X} (h : a .rv = b .rv) :
    a = b := by
  funext s j
  cases s with
  | vf => exact j.elim
  | rv => exact congrFun h j

/-- View an injectively labelled object as its set of labels. -/
def structureLabelEquiv (U : RVObject M S k) (inj : Function.Injective U.label) :
    U.carrier ≃ structureLabels U :=
  Equiv.ofInjective (rvTupleAssignment ∘ U.label) (fun _ _ eq => inj (congrFun eq .rv))

theorem structureLabelEquiv_apply (U : RVObject M S k) (inj : Function.Injective U.label) (x : U.carrier) :
    structureLabelEquiv U inj x = structureLabel U x := by
  rfl

/-- The graph on the structure labels comes from composing the two
structure graphs with the original isomorphism. -/
theorem injective_label_map_definable (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun u => (e u).val)))
    (iU : Function.Injective U.label) (iV : Function.Injective V.label) :
    let g := (structureLabelEquiv U iU).symm.trans (e.trans (structureLabelEquiv V iV))
    DefinableRelation M S.carrier
      (fun a b => ∃ ha : a ∈ structureLabels U, (g ⟨a,ha⟩).val = b) := by
  intro g
  have l := relation_of_rvGraph U.graph
  have m := relation_of_rvGraph eDef
  have r := relation_of_rvGraph V.graph
  apply ((l.transpose.comp m).comp r).congr
  intro a b
  constructor
  · rintro ⟨w,⟨u,⟨x,hxu,hxa⟩,y,hyu,hyw⟩,z,hzw,hzb⟩
    have hxy : x = y := Subtype.ext (hxu.trans hyu.symm)
    have hz : z = e x := Subtype.ext (hzw.trans (hxy ▸ hyw).symm)
    have ha : (structureLabel U x).val = a := rvAssignment_ext hxa
    have hb : (structureLabel V (e x)).val = b := rvAssignment_ext (hz ▸ hzb)
    have hx := (structureLabel U x).property
    refine ⟨ha ▸ hx,?_⟩
    have h : (⟨a,ha ▸ hx⟩ : structureLabels U) = structureLabelEquiv U iU x :=
      Subtype.ext ha.symm
    rw [h]
    change (structureLabelEquiv V iV (e ((structureLabelEquiv U iU).symm
      (structureLabelEquiv U iU x)))).val = b
    rw [Equiv.symm_apply_apply, structureLabelEquiv_apply]
    exact hb
  · rintro ⟨ha,hb⟩
    let x := (structureLabelEquiv U iU).symm ⟨a,ha⟩
    have hxa : U.label x = a .rv :=
      congrFun (congrArg Subtype.val ((structureLabelEquiv U iU).apply_symm_apply ⟨a,ha⟩)) .rv
    have hxb : V.label (e x) = b .rv := congrFun hb .rv
    exact ⟨rvTupleAssignment (e x).val,⟨rvTupleAssignment x.val,⟨x,rfl,hxa⟩,x,rfl,rfl⟩,
      e x,rfl,hxb⟩

/-- Lift an RV isomorphism of injectively labelled objects using the
lifting theorem for sets of RV labels. -/
theorem definable_lift_of_injective_labels (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun u => (e u).val)))
    (iU : Function.Injective U.label) (iV : Function.Injective V.label)
    (liftSets : ∀ (g : structureLabels U ≃ structureLabels V),
      DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ structureLabels U, (g ⟨a,ha⟩).val = b) →
      HasDefinableFieldLift S g) :
    HasDefinableObjectLift U V e := by
  let g := (structureLabelEquiv U iU).symm.trans (e.trans (structureLabelEquiv V iV))
  have h (x : U.carrier) : g (structureLabel U x) = structureLabel V (e x) := by
    change structureLabelEquiv V iV (e ((structureLabelEquiv U iU).symm
      (structureLabelEquiv U iU x))) = _
    rw [Equiv.symm_apply_apply, structureLabelEquiv_apply]
  exact definable_lift_of_compatible_labels U V e eDef g h
    (liftSets g (injective_label_map_definable U V e eDef iU iV))

end GeneralizedEuler.Section5.ObjectLift
