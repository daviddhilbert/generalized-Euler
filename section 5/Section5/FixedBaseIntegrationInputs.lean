module

public import Section5.IntegrationIsomorphism
public import Section5.CanonicalObjectLift

/-! Obtain the inputs to integration from the fixed-base lifting,
preparation and chart hypotheses. The elementary relation and the
comparison of contraction orders are consequences of these inputs. -/

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
local notation "Z" => CanonicalSort O

def integrationInputs_of_geometry
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (hyp' : ∀ n (p : fieldAssignment n Z), FieldwiseContractionHypotheses ((𝓜).termGenerated (namedTuple S p)))
    (head' : ∀ n (p : fieldAssignment n Z), HeadPreparationHypotheses O hO power ((𝓜).termGenerated (namedTuple S p)))
    (chart : ∀ n (p : fieldAssignment n Z), PositioningChartHypotheses ((𝓜).termGenerated (namedTuple S p)))
    (recovery : UnaryRecoveryHypotheses S)
    (eps : K) (he : eps ≠ 0) (small : O.valuation eps < 1) (zero : S.carrier .vf) (hz : zero.val = 0)
    (satRV : ∀ k (D : ℕ → Set (Fin k → RV0 O)), (∀ i, isRVSet 𝓜 S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (liftSets : ∀ k (A B : Set (labelAssignment k Z)) (g : A ≃ B),
      SortedDefinableOver 𝓜 S.carrier A → SortedDefinableOver 𝓜 S.carrier B →
      DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ A, (g ⟨a,ha⟩).val = b) →
      (∀ a ∈ A, ∀ j, a .rv j ≠ 0) → (∀ b ∈ B, ∀ j, b .rv j ≠ 0) → HasDefinableFieldLift S g)
    (satZero : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables 0 Empty))
      (BaseAssignments S.carrier (MixedVariables 0 Empty)))
    (elem : ∀ a : fieldAssignment 0 Z,
      let B := (𝓜).termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize 𝓜 (fun s i => (v s i).val)) :
    IntegrationHypotheses S neg := by
  let liftIso : LiftsRVIsomorphisms 𝓜 S := liftsRVIsomorphisms_of_label_lifts O hO power S satRV liftSets
  exact
    { fieldwise := hyp
      head := head
      exchange := two_coordinate_comparison_at_field_bases S neg hyp' head' chart he small zero hz
      recovery := recovery
      infinitesimal := eps
      infinitesimal_ne := he
      infinitesimal_small := small
      zero := zero
      zero_eq := hz
      liftIso := liftIso
      pointRelation := liftClassHom_point_blowup O hO power S neg liftIso (satRV 0) satZero elem
        head.fieldTerms head.minusOne head.minusOne_realizes head.fieldTerms_realize }

end GeneralizedEuler.Section5
