module

public import Section5.PreparedUnaryKernel
public import Section5.InjectiveObjectLifts

/-! A degree-one lift is a unary pullback with the original RV tag.
Its active field leading term reads the structure label of the tag. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable (U : RVObject (canonicalStructure (L := L) O hO power) S 1)

@[expose] def unaryLiftSet : Set (K × (Fin U.arity → RV0 O)) :=
  {x : K × (Fin U.arity → RV0 O) | ∃ t : U.carrier, t.val = x.2 ∧ U.label t 0 = rv O x.1}

theorem mem_unaryLiftSet (x : SortedAssignment (CanonicalSort O) (ObjectLift.Vars U)) :
    unaryPair O x ∈ unaryLiftSet O hO power S U ↔ x ∈ ObjectLift.carrier U := by
  change (∃ t : U.carrier, t.val = x .rv ∧ U.label t 0 = rv O (x .vf 0)) ↔
    ∃ t : U.carrier, t.val = x .rv ∧ U.label t = (𝓜).rvMap ∘ x .vf
  constructor
  · rintro ⟨t,ht,h⟩
    refine ⟨t,ht,funext fun i => ?_⟩
    rw [Subsingleton.elim i (0 : Fin 1)]
    exact h.trans (canonicalStructure_rvMap O hO power _).symm
  · rintro ⟨t,ht,h⟩
    exact ⟨t,ht,(congrFun h 0).trans (canonicalStructure_rvMap O hO power _)⟩

theorem unaryLiftSet_definable : UnaryPullbackDefinable O hO power S (unaryLiftSet O hO power S U) := by
  convert ObjectLift.definable U using 1
  ext x
  exact mem_unaryLiftSet O hO power S U x

@[expose] def unaryLiftEquiv : ObjectLift.carrier U ≃ unaryLiftSet O hO power S U :=
  (Set.equivOfEq (Set.ext fun x => (mem_unaryLiftSet O hO power S U x).symm)).trans
    (unaryAssignmentEquiv O (unaryLiftSet O hO power S U))

theorem unaryLiftEquiv_apply (x : ObjectLift.carrier U) :
    (unaryLiftEquiv O hO power S U x).val = unaryPair O x.val := rfl

theorem unaryLiftSet_pullback : IsUnaryPullback O (unaryLiftSet O hO power S U) := by
  rintro x ⟨t,ht,h⟩ y label
  exact ⟨t,ht.trans (congrArg (fun w : RV0 O × (Fin U.arity → RV0 O) => w.2) label),
    h.trans (congrArg (fun w : RV0 O × (Fin U.arity → RV0 O) => w.1) label)⟩

theorem unaryLiftSet_finite : UnaryFiniteFibers (unaryLiftSet O hO power S U) := by
  intro x
  let lead : Fin 1 → RV0 O := fun _ => rv O x
  apply ((U.finiteFibers lead).image Subtype.val).subset
  rintro y ⟨t,ht,h⟩
  refine ⟨t,?_,ht⟩
  change U.label t = lead
  funext i
  rw [Subsingleton.elim i (0 : Fin 1)]
  exact h

@[expose] def totalUnaryLabel (x : Fin U.arity → RV0 O) : RV0 O := by
  classical
  exact if h : x ∈ U.carrier then U.label ⟨x,h⟩ 0 else 0

theorem totalUnaryLabel_definable : DefinableRelation 𝓜 S.carrier
    (fun (a : SortedAssignment (CanonicalSort O) (RVVariables (Fin U.arity)))
      (b : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1))) =>
      totalUnaryLabel O hO power S U (a .rv) = b .rv 0) := by
  classical
  let W := SumVariables (RVVariables (Fin U.arity)) (RVVariables (Fin 1))
  have zero := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inr 0) rvZeroTerm
  have z : DefinableRelation 𝓜 S.carrier (fun
      (_ : SortedAssignment (CanonicalSort O) (RVVariables (Fin U.arity)))
      (b : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1))) => b .rv 0 = 0) := by
    unfold DefinableRelation
    convert zero using 1
    ext a
    simp only [Set.mem_ofPred_eq,realize_rvZeroTerm O hO power]
    rfl
  have graph := ObjectLift.relation_of_rvGraph U.graph
  refine (graph.union (z.inter_left U.definable.compl)).congr ?_
  intro a b
  change ((∃ x : U.carrier, x.val = a .rv ∧ U.label x = b .rv) ∨
    (b .rv 0 = 0 ∧ a .rv ∉ U.carrier)) ↔ totalUnaryLabel O hO power S U (a .rv) = b .rv 0
  unfold totalUnaryLabel
  by_cases h : a .rv ∈ U.carrier
  · rw [dite_eq_left h]
    constructor
    · rintro (⟨x,eq,hx⟩ | ⟨_,hn⟩)
      · have same : x = ⟨a .rv,h⟩ := Subtype.ext eq
        rw [← same]
        exact congrFun hx 0
      · exact (hn h).elim
    · intro eq
      refine Or.inl ⟨⟨a .rv,h⟩,rfl,funext fun j => ?_⟩
      rwa [Subsingleton.elim j (0 : Fin 1)]
  · rw [dite_eq_right h]
    exact ⟨fun ht => ht.elim (fun ⟨x,eq,_⟩ => (h (eq ▸ x.property)).elim) (fun hz => hz.1.symm),
      fun eq => Or.inr ⟨eq.symm,h⟩⟩

end GeneralizedEuler.Section5
