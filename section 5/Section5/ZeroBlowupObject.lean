module

public import Section5.InjectiveObjectLifts
public import Section5.LabelProjection

/-! The degree-lowered RV object carried by the zero multiplier. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {n k : ℕ}

theorem rvGraph_of_relation {I J : Type} {D : Set (I → X .rv)} {f : D → J → X .rv}
    (h : DefinableRelation M S.carrier
      (fun a : SortedAssignment X (RVVariables I) => fun b : SortedAssignment X (RVVariables J) =>
        ∃ x : D, x.val = a .rv ∧ f x = b .rv)) :
    SortedDefinableOver M S.carrier (rvGraph f) := by
  let r : ∀ s, SumVariables (RVVariables I) (RVVariables J) s → RVVariables (I ⊕ J) s
    | .vf => Sum.elim PEmpty.elim PEmpty.elim
    | .rv => id
  exact h.pullback_relabel r

theorem rvLabelProjection_definable (U : RVObject M S n) (p : Fin k → Fin n) :
    SortedDefinableOver M S.carrier (rvGraph (fun a => U.label a ∘ p)) := by
  have h := (ObjectLift.relation_of_rvGraph U.graph).comp
    (projectLabels_definable (M := M) (S := S) p)
  apply rvGraph_of_relation (h.congr ?_)
  intro a b
  constructor
  · rintro ⟨t,⟨u,hu,ht⟩,hEq⟩
    exact ⟨u,hu,congrArg (fun x => x ∘ p) ht |>.trans (congrFun hEq .rv)⟩
  · rintro ⟨u,hu,ht⟩
    refine ⟨rvTupleAssignment (U.label u),⟨u,hu,rfl⟩,?_⟩
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => exact congrFun ht i

/-- Deleting the blown-up coordinate gives the zero layer. The finite
deletion hypothesis is imposed on the image of the original map. -/
@[expose] def zeroBlowupObject (U : RVObject M S (k+1)) (j : Fin (k+1))
    (finiteDelete : ∀ t : Fin k → X .rv, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    RVObject M S k where
  arity := U.arity
  carrier := U.carrier
  definable := U.definable
  label a := U.label a ∘ j.succAbove
  graph := rvLabelProjection_definable U j.succAbove
  nonzero a i := U.nonzero a (j.succAbove i)
  finiteFibers t := by
    apply ((finiteDelete t).biUnion (fun u _ => U.finiteFibers u)).subset
    intro a ha
    exact Set.mem_iUnion₂.mpr ⟨U.label a,⟨Set.mem_range_self a,ha⟩,rfl⟩

end GeneralizedEuler.Section5
