module

public import Section5.UnaryLiftClassComparison
import all Section5.UnaryTranslationClass
import all Section4.Objects

/-! Pad degree-zero lifts by a single zero field coordinate. The
unary pullback carries no active RV label and recovers the same class. -/

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
  (U : RVObject (canonicalStructure (L := L) O hO power) S 0)

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def unaryZeroLiftSet : Set (K × (Fin U.arity → RV0 O)) :=
  {x : K × (Fin U.arity → RV0 O) | x.1 = 0 ∧ x.2 ∈ U.carrier}

theorem unaryZeroLiftSet_definable : UnaryPullbackDefinable O hO power S (unaryZeroLiftSet O hO power S U) := by
  let W := MixedVariables 1 (Fin U.arity)
  let r : ∀ s, RVVariables (Fin U.arity) s → W s
    | .vf => PEmpty.elim
    | .rv => id
  exact (field_eq_zero_definable O hO power S (V := W) 0).inter (U.definable.pullback_relabel r)

theorem unaryZeroLiftSet_pullback : IsUnaryPullback O (unaryZeroLiftSet O hO power S U) := by
  rintro x ⟨hz,ht⟩ y eq
  have e : rv O x.1 = rv O y.1 := congrArg Prod.fst eq
  rw [hz,map_zero] at e
  exact ⟨(rv_eq_zero_iff O).1 e.symm,(congrArg (fun w : RV0 O × (Fin U.arity → RV0 O) => w.2) eq) ▸ ht⟩

theorem unaryZeroLiftSet_finite : UnaryFiniteFibers (unaryZeroLiftSet O hO power S U) := by
  intro x
  have finite := (U.finiteFibers Fin.elim0).image Subtype.val
  apply finite.subset
  rintro t ⟨_,ht⟩
  exact ⟨⟨t,ht⟩,Subsingleton.elim _ _,rfl⟩

@[expose] def unaryZeroLiftIndex : Fin (U.arity+1) ≃ Fin 1 ⊕ Fin U.arity :=
  finSumFinEquiv.symm.trans (Equiv.sumComm _ _)

theorem unaryZeroLift_labelSet :
    reindexedUnaryLabels O (unaryZeroLiftSet O hO power S U) (unaryZeroLiftIndex O hO power S U) =
      appendUnaryLabelSet O U.carrier (fun _ b => b = 0) := by
  ext w
  let t := w ∘ (unaryZeroLiftIndex O hO power S U).symm
  let r := t ∘ Sum.inr
  let b := t (.inl 0)
  change t ∈ unaryLabelSet O (unaryZeroLiftSet O hO power S U) ↔ r ∈ U.carrier ∧ b = 0
  rw [unaryLabelSet_iff_decoded O t]
  constructor
  · rintro ⟨x,⟨hz,ht⟩,eq⟩
    have hf : rv O x.1 = b := congrArg Prod.fst eq
    rw [hz,map_zero] at hf
    have eqTag : x.2 = r := congrArg (fun w : RV0 O × (Fin U.arity → RV0 O) => w.2) eq
    exact ⟨eqTag ▸ ht,hf.symm⟩
  · rintro ⟨hr,hb⟩
    exact ⟨(0,r),⟨rfl,hr⟩,Prod.ext ((map_zero (rv O)).trans hb.symm) rfl⟩

theorem unaryZeroLift_labelClass :
    unaryLabelClass O hO power S (unaryZeroLiftSet O hO power S U) (unaryZeroLiftIndex O hO power S U)
      (unaryZeroLiftSet_definable O hO power S U) (unaryZeroLiftSet_pullback O hO power S U)
      (unaryZeroLiftSet_finite O hO power S U) = objectClass 𝓜 S ⟨0,U⟩ := by
  let A := unaryZeroLiftSet O hO power S U
  let i := unaryZeroLiftIndex O hO power S U
  let V := unaryLabelObjects O hO power S A i (unaryZeroLiftSet_definable O hO power S U)
    (unaryZeroLiftSet_pullback O hO power S U) (unaryZeroLiftSet_finite O hO power S U)
  have zero (w : Fin (U.arity+1) → RV0 O) (h : w ∈ reindexedUnaryLabels O A i) : w (i.symm (.inl 0)) = 0 := by
    have member : w ∈ appendUnaryLabelSet O U.carrier (fun _ b => b = 0) :=
      (unaryZeroLift_labelSet O hO power S U) ▸ h
    exact member.2
  have empty : V.2.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro w h
    exact h.2 (zero w h.1)
  have clsEmpty : objectClass 𝓜 S ⟨1,V.2⟩ = 0 := scissors_sound 𝓜 S (RVRelation.zero V.2 empty)
  have take : V.1.carrier = reindexedUnaryLabels O A i := by
    ext w
    exact ⟨fun h => h.1,fun h => ⟨h,zero w h⟩⟩
  change objectClass 𝓜 S ⟨0,V.1⟩ + objectClass 𝓜 S ⟨1,V.2⟩ = _
  rw [clsEmpty,add_zero]
  apply scissors_sound 𝓜 S
  apply RVRelation.iso
  change RVDefinablyEquivalent 𝓜 S.carrier V.1.carrier U.carrier
  rw [take.trans (unaryZeroLift_labelSet O hO power S U)]
  exact (appendZeroLabel_equiv O hO power S U.carrier U.definable).symm

end GeneralizedEuler.Section5
