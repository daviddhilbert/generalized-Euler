module

public import Section5.RelativeRVObjectSchemes
public import Section5.FieldClassBaseExtension

/-! An RV object over the original base gives a constant relative
object. Its fibers are the same lift with the larger named base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type} {k : ℕ}
  (U : RVObject M S k) (bound : ℕ)

@[expose] def constantRelativeRVObject : RelativeRVObjectScheme M S P where
  data :=
    { degree := k
      arity := U.arity
      tags := {a | a .rv ∘ Sum.inr ∈ U.carrier}
      definable := U.definable.pullback_relabel (fun _ => Sum.inr) }
  graph := {a | ∃ u : U.carrier, u.val = a .rv ∘ Sum.inl ∘ Sum.inr ∧ U.label u = a .rv ∘ Sum.inr}
  definable := by
    let rename : ∀ s, RVVariables (Fin U.arity ⊕ Fin k) s →
        SumVariables (SumVariables P (RVVariables (Fin U.arity))) (RVVariables (Fin k)) s
      | .vf => PEmpty.elim
      | .rv => Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
    exact U.graph.pullback_relabel rename
  bound := bound

theorem constantRelativeRVObject_valid (p : SortedAssignment X P) (zero : S.carrier .rv)
    (hz : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (finite : ∀ (x : Fin k → X .rv) (a : Fin (bound+1) → U.carrier),
      (∀ i, U.label (a i) = x) → ¬ Function.Injective a) :
    (constantRelativeRVObject (P := P) U bound).valid zero p := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u
    constructor
    · intro hu
      exact ⟨rvTupleAssignment (U.label ⟨u .rv,hu⟩),⟨u .rv,hu⟩,rfl,rfl⟩
    · rintro ⟨v,a,eq,_⟩
      change u .rv ∈ U.carrier
      have e : a.val = u .rv := eq
      exact e ▸ a.property
  · rintro u v w ⟨a,ha,hv⟩ ⟨b,hb,hw⟩
    have eq : a = b := Subtype.ext (ha.trans hb.symm)
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => exact congrFun (hv.symm.trans ((congrArg U.label eq).trans hw)) i
  · rintro u v ⟨a,_,e⟩ i
    rw [hz]
    have label : U.label a i = v .rv i := congrFun e i
    exact label ▸ U.nonzero a i
  · intro v a ha inj
    have witness (i : Fin (bound+1)) : ∃ x : U.carrier, x.val = (a i) .rv ∧ U.label x = v .rv := ha i
    choose f hf hg using witness
    apply finite (v .rv) f hg
    intro i j eq
    apply inj
    funext s r
    cases s with
    | vf => exact r.elim
    | rv => exact congrFun ((hf i).symm.trans ((congrArg Subtype.val eq).trans (hf j))) r

theorem base_subset_named (p : SortedAssignment X P) :
    ∀ s, S.carrier s ⊆ (M.termGenerated (namedTuple S p)).carrier s :=
  fun s _ h => (M.termGeneratedAssignment (namedTuple S p) s (Sum.inl ⟨_,h⟩)).property

theorem constantRelativeRVObject_fiber_lift_eq (p : SortedAssignment X P) :
    {x : SortedAssignment X (MixedVariables k (Fin U.arity)) |
      appendAssignments p x ∈ relativeRVLift (M := M) (constantRelativeRVObject (P := P) U bound).graph} =
      ObjectLift.carrier U :=
  rfl

theorem constantRelativeRVObject_lift_eq (p : SortedAssignment X P) (zero : S.carrier .rv)
    (hz : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (valid : (constantRelativeRVObject (P := P) U bound).valid zero p) :
    ObjectLift.carrier ((constantRelativeRVObject (P := P) U bound).realize zero hz p valid) =
      ObjectLift.carrier U := by
  have w : RelativeRVWitness (constantRelativeRVObject (P := P) U bound).data.tags
    (constantRelativeRVObject (P := P) U bound).graph (M.funMap .rvZero (fun i => i.elim0))
    (constantRelativeRVObject (P := P) U bound).bound p := by
    simpa only [RelativeRVObjectScheme.valid,hz] using valid
  exact (realizedRelativeRVObject_lift_eq p _ _ w).symm

theorem constantRelativeRVObject_lift_class [TopologicalSpace (X .vf)]
    (p : SortedAssignment X P) (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (valid : (constantRelativeRVObject (P := P) U bound).valid zero p) :
    liftObjectClass ⟨k,(constantRelativeRVObject (P := P) U bound).realize zero hz p valid⟩ =
      fieldClassBaseExtension (base_subset_named (S := S) p) (liftObjectClass ⟨k,U⟩) := by
  rw [show liftObjectClass ⟨k,U⟩ = fieldClass M S ⟨k,liftFieldObject U⟩ from rfl,fieldClassBaseExtension_class]
  apply fieldClass_of_iso M _
  change MixedDefinablyEquivalent M _
    (ObjectLift.carrier ((constantRelativeRVObject (P := P) U bound).realize zero hz p valid)) (ObjectLift.carrier U)
  rw [constantRelativeRVObject_lift_eq U bound p zero hz valid]
  exact .refl ((ObjectLift.definable U).mono (base_subset_named p))

end GeneralizedEuler.Section5
