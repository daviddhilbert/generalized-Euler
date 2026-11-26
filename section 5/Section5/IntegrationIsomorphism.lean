module

public import Section5.PositiveLiftKernel
public import Section5.BlowupLiftClass
public import Section5.FieldClassPreparation
public import Section5.FieldBaseOrderComparison
public import Section5.GroupifiedBlowupQuotient

/-! The fixed-base lift identifies the positive VF scissor semiring
with the graded RV semiring modulo common blowups. Groupification
identifies the VF ring with the quotient by the elementary ideal. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Q" => (gradedBlowupCongruence O hO power S neg)

structure IntegrationHypotheses where
  fieldwise : FieldwiseContractionHypotheses S
  head : HeadPreparationHypotheses O hO power S
  exchange : TwoCoordinateComparisonAtFieldBases S neg
  recovery : UnaryRecoveryHypotheses S
  infinitesimal : K
  infinitesimal_ne : infinitesimal ≠ 0
  infinitesimal_small : O.valuation infinitesimal < 1
  zero : S.carrier .vf
  zero_eq : zero.val = 0
  liftIso : LiftsRVIsomorphisms 𝓜 S
  pointRelation : liftClassHom liftIso (residuePointClass O hO power S) =
    liftClassHom liftIso (1 + multiplierClass O hO power S neg)

theorem liftClassHom_eq_iff_common_blowup (H : IntegrationHypotheses S neg) (a b : RVSemiring 𝓜 S) :
    liftClassHom H.liftIso a = liftClassHom H.liftIso b ↔
      CommonBlowup (ElementaryClassStep O hO power S neg) a b := by
  constructor
  · exact common_blowup_of_equal_lift_classes S neg H.fieldwise H.head H.exchange H.recovery
      H.infinitesimal_ne H.infinitesimal_small H.zero H.zero_eq H.liftIso
  · intro eq
    have g : ((Q).mk') a = ((Q).mk') b := Quotient.sound eq
    simpa only [quotientLiftClassHom_mk] using
      congrArg (quotientLiftClassHom O hO power S neg H.liftIso H.pointRelation) g

/-- The forward map is the lift, so its inverse is positive integration. -/
def positiveLiftEquiv (H : IntegrationHypotheses S neg) : (Q).Quotient ≃+* VFSemiring 𝓜 S := by
  let f := quotientLiftClassHom O hO power S neg H.liftIso H.pointRelation
  apply RingEquiv.ofBijective f
  constructor
  · rintro ⟨a⟩ ⟨b⟩ eq
    change quotientLiftClassHom O hO power S neg H.liftIso H.pointRelation ((Q).mk' a) =
      quotientLiftClassHom O hO power S neg H.liftIso H.pointRelation ((Q).mk' b) at eq
    rw [quotientLiftClassHom_mk,quotientLiftClassHom_mk] at eq
    exact Quotient.sound ((liftClassHom_eq_iff_common_blowup S neg H a b).1 eq)
  · apply quotientLiftClassHom_surjective
    exact liftClassHom_surjective O hO power S H.liftIso H.head.minusOne H.head.minusOne_realizes
      H.head.fieldTerms H.head.fieldTerms_realize H.head.saturated H.head.immediate

theorem positiveLiftEquiv_mk (H : IntegrationHypotheses S neg) (a : RVSemiring 𝓜 S) :
    positiveLiftEquiv S neg H ((Q).mk' a) = liftClassHom H.liftIso a := by
  change quotientLiftClassHom O hO power S neg H.liftIso H.pointRelation ((Q).mk' a) = _
  exact quotientLiftClassHom_mk O hO power S neg H.liftIso H.pointRelation a

theorem positiveIntegral_lift (H : IntegrationHypotheses S neg) (a : RVSemiring 𝓜 S) :
    (positiveLiftEquiv S neg H).symm (liftClassHom H.liftIso a) = (Q).mk' a := by
  rw [← positiveLiftEquiv_mk S neg H a, RingEquiv.symm_apply_apply]

def groupifyRingEquiv {A B : Type*} [CommSemiring A] [CommSemiring B] (e : A ≃+* B) :
    SemiringGroupification.Ring A ≃+* SemiringGroupification.Ring B :=
  RingEquiv.ofRingHom (SemiringGroupification.map e.toRingHom) (SemiringGroupification.map e.symm.toRingHom)
    (SemiringGroupification.hom_ext (fun b => by simp [RingHom.comp_apply]))
    (SemiringGroupification.hom_ext (fun a => by simp [RingHom.comp_apply]))

def ringIntegrationEquiv (H : IntegrationHypotheses S neg) :
    GeneralizedEuler.Section4.SemiringGroupification.Ring (VFSemiring 𝓜 S) ≃+*
      (GeneralizedEuler.Section4.SemiringGroupification.Ring (RVSemiring 𝓜 S) ⧸
      elementaryBlowupIdeal O hO power S neg) :=
  (groupifyRingEquiv (positiveLiftEquiv S neg H).symm).trans
    (groupifiedBlowupQuotientEquiv O hO power S neg).symm

end GeneralizedEuler.Section5
