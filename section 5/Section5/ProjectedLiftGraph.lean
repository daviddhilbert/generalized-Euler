module

public import Section5.LabelProjection
public import Mathlib.Logic.Equiv.Set

/-! The fixed-base RV graph on two injectively projected pieces. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n k : ℕ} {U V : Set (labelAssignment n X)}

/-- Pass a label bijection through two injective coordinate projections. -/
def projectedLabelEquiv (e : U ≃ V) (p q : Fin k → Fin n)
    (hp : Set.InjOn (projectLabels p) U) (hq : Set.InjOn (projectLabels q) V) :
    (projectLabels p '' U : Set (labelAssignment k X)) ≃
      (projectLabels q '' V : Set (labelAssignment k X)) :=
  (Equiv.Set.imageOfInjOn (projectLabels p) U hp).symm.trans
    (e.trans (Equiv.Set.imageOfInjOn (projectLabels q) V hq))

theorem projectedLabelEquiv_apply (e : U ≃ V) (p q : Fin k → Fin n)
    (hp : Set.InjOn (projectLabels p) U) (hq : Set.InjOn (projectLabels q) V) (a : U) :
    (projectedLabelEquiv e p q hp hq ⟨projectLabels p a.val,Set.mem_image_of_mem _ a.property⟩).val =
      projectLabels q (e a).val := by
  let P := Equiv.Set.imageOfInjOn (projectLabels p) U hp
  change projectLabels q (e (P.symm (P a))).val = _
  rw [P.symm_apply_apply]

theorem projectedLabelEquiv_definable (e : U ≃ V) (p q : Fin k → Fin n)
    (hp : Set.InjOn (projectLabels p) U) (hq : Set.InjOn (projectLabels q) V)
    (he : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b)) :
    DefinableRelation M S.carrier
      (fun a b => ∃ ha : a ∈ projectLabels p '' U,
        (projectedLabelEquiv e p q hp hq ⟨a,ha⟩).val = b) := by
  let Q := Equiv.Set.imageOfInjOn (projectLabels p) U hp
  have hP := projectLabels_definable (M := M) (S := S) p
  have hQ := projectLabels_definable (M := M) (S := S) q
  apply ((hP.transpose.comp he).comp hQ).congr
  intro a b
  constructor
  · rintro ⟨_,⟨u,rfl,hu,rfl⟩,rfl⟩
    exact ⟨Set.mem_image_of_mem _ hu,projectedLabelEquiv_apply e p q hp hq ⟨u,hu⟩⟩
  · rintro ⟨ha,he⟩
    let u := Q.symm ⟨a,ha⟩
    have hu : projectLabels p u.val = a := congrArg Subtype.val (Q.apply_symm_apply ⟨a,ha⟩)
    have hv : projectLabels q (e u).val = b := by
      rw [← projectedLabelEquiv_apply e p q hp hq u]
      change (projectedLabelEquiv e p q hp hq (Q u)).val = b
      rwa [show Q u = ⟨a,ha⟩ from Q.apply_symm_apply ⟨a,ha⟩]
    exact ⟨(e u).val,⟨u.val,hu,u.property,rfl⟩,hv⟩

/-- Select VF coordinates in the same order as their RV projection. -/
@[expose] def projectFields (p : Fin k → Fin n) (a : fieldAssignment n X) : fieldAssignment k X :=
  fieldTupleAssignment (a .vf ∘ p)

theorem projectFields_definable (p : Fin k → Fin n) :
    DefinableRelation M S.carrier (fun a b => projectFields p a = b) := by
  let V := SumVariables (MixedVariables n Empty) (MixedVariables k Empty)
  have h := SortedDefinableOver.iInter (fun i : Fin k =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V) .vf
      (.inl (p i)) (.inr i))
  unfold DefinableRelation
  convert h using 1
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro eq i
    exact congrFun (congrFun eq .vf) i
  · intro eq
    funext s i
    cases s with
    | vf => exact eq i
    | rv => exact i.elim

theorem projectFields_fieldLead (p : Fin k → Fin n) (a : fieldAssignment n X) :
    fieldLead M (projectFields p a) = projectLabels p (fieldLead M a) := by
  funext s j
  cases s with
  | vf => exact j.elim
  | rv => rfl

end GeneralizedEuler.Section5
