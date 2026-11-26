module

public import Section5.FixedBaseContractionInvariance

/-! A fixed-base isomorphism of lifts, even in different original
degrees, forces a common blowup after both lifts are padded to one
positive field arity. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem paddedLiftFamily_carrier_eq {d n : ℕ} (U : RVObject 𝓜 S d) (p : Fin d ↪ Fin n) :
    {a : SortedAssignment Z (MixedVariables n (Fin U.arity)) |
      mixedTuple a ∈ (paddedLiftFamily O hO power S U p).carrier} =
      paddedLiftCarrier O hO power S U p (Equiv.refl _) := by
  ext a
  have mapRV : (𝓜).rvMap = rv O := funext (canonicalStructure_rvMap O hO power)
  change ((∃ u : U.carrier, u.val = a .rv ∧ U.label u = rv O ∘ a .vf ∘ p) ∧
    ∀ i ∉ Set.range p, a .vf i = 0) ↔
    ((∃ u : U.carrier, u.val = a .rv ∧ U.label u = (𝓜).rvMap ∘ a .vf ∘ p) ∧
    ∀ i ∉ Set.range p, a .vf i = 0)
  rw [mapRV]

theorem common_blowup_of_isomorphic_lifts
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg) (recovery : UnaryRecoveryHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (zero : S.carrier .vf) (hz : zero.val = 0)
    {d e : ℕ} (U : RVObject 𝓜 S d) (V : RVObject 𝓜 S e)
    (iso : MixedDefinablyEquivalent 𝓜 S (ObjectLift.carrier U) (ObjectLift.carrier V)) :
    CommonBlowup (ElementaryClassStep O hO power S neg) (objectClass 𝓜 S ⟨d,U⟩) (objectClass 𝓜 S ⟨e,V⟩) := by
  let n := max d e
  let p : Fin d ↪ Fin (n+1) := Fin.castLEEmb ((le_max_left d e).trans (Nat.le_succ _))
  let q : Fin e ↪ Fin (n+1) := Fin.castLEEmb ((le_max_right d e).trans (Nat.le_succ _))
  let A := paddedLiftFamily O hO power S U p
  let B := paddedLiftFamily O hO power S V q
  have f : MixedDefinablyEquivalent 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier} := by
    change MixedDefinablyEquivalent 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) (Fin U.arity)) |
        mixedTuple a ∈ (paddedLiftFamily O hO power S U p).carrier}
      {a : SortedAssignment Z (MixedVariables (n+1) (Fin V.arity)) |
        mixedTuple a ∈ (paddedLiftFamily O hO power S V q).carrier}
    rw [paddedLiftFamily_carrier_eq S U p,paddedLiftFamily_carrier_eq S V q]
    exact (paddedLift_iso O hO power S U p (Equiv.refl _)).trans
      (iso.trans (paddedLift_iso O hO power S V q (Equiv.refl _)).symm)
  have comparison := contractionValue_of_mixed_iso S neg hyp head pair recovery he small zero f
  have left := contractionValue_padded_lift S neg hyp head zero hz U p
  have right := contractionValue_padded_lift S neg hyp head zero hz V q
  exact Quotient.exact (left.symm.trans (comparison.trans right))

end GeneralizedEuler.Section5
