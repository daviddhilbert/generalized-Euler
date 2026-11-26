module

public import Section5.PositiveFubini
public import Section5.UniformGradedLiftPresentations

/-! The fixed-base preparation theorem produces the graded covers
required to represent the inner integrals along any projection. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {b n m q : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables b Empty

theorem projection_graded_lift_cover_of_preparation
    (e : Fin (b+n) ≃ Fin q) (A : Set (SortedAssignment Z (MixedVariables q (Fin m))))
    (d : SortedDefinableOver 𝓜 S.carrier A)
    (finite : ∀ x : Fin q → K, {r | (x,r) ∈ mixedTuple '' A}.Finite)
    (head : HeadPreparationHypotheses O hO power S)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (localHead : ∀ p ∈ fieldProjection (splitFieldSpace e A),
      HeadPreparationHypotheses O hO power (relativeBase S p))
    (localLabel : ∀ p ∈ fieldProjection (splitFieldSpace e A), ∀ k,
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase (relativeBase S p).carrier (RVVariables (Fin k)))
        (BaseAssignments (relativeBase S p).carrier (RVVariables (Fin k)))) :
    Nonempty (GradedLiftCover 𝓜 S (fieldProjection (splitFieldSpace e A)) (splitFieldSpace e A) (baseRVZero S)) := by
  let B := splitFieldSpace e A
  let D := fieldProjection B
  have db := splitFieldSpace_definable e d
  have dd := fieldProjection_definable db
  obtain ⟨C,parts,defParts,valid,disj,cover⟩ := uniform_relative_mixed_lifts O hO power S D dd B db
    head.fieldTerms head.minusOne head.minusOne_realizes head.fieldTerms_realize sat
    (fun p hp => (localHead p hp).saturated) localLabel (fun p hp => (localHead p hp).immediate)
    (fun p _ => splitFieldSpace_finite_fibers e finite p)
  exact ⟨⟨C,parts,defParts,valid,disj,cover⟩⟩

end GeneralizedEuler.Section5
