module

public import Section5.FixedBaseContractionInvariance
public import Section5.MixedTaggedGraphCuts

/-! An isomorphism of mixed tagged unions compares the sum of the
contraction classes. The two sums refine to the entries of its graph. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n p q : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Q" => (gradedBlowupCongruence O hO power S neg)

@[expose] def taggedMixedCarriers {r : ℕ} (I : Fin r → Type) [∀ i, Finite (I i)]
    (A : ∀ i, MixedCarrier Z n (I i)) (defA : ∀ i, SortedDefinableOver 𝓜 S.carrier (A i)) :
    MixedTaggedFamily 𝓜 S where
  Tag := Fin r
  coordinates i := MixedVariables n (I i)
  finiteCoordinates i s := by
    cases s with
    | vf => exact inferInstanceAs (Finite (Fin n))
    | rv => exact inferInstanceAs (Finite (I i))
  piece := A
  definable := defA

theorem sum_mixedContractionValue_of_tagged_iso
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg) (recovery : UnaryRecoveryHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1) (basePoint : S.carrier .vf)
    (I : Fin p → Type) (J : Fin q → Type) [∀ i, Finite (I i)] [∀ j, Finite (J j)]
    (A : ∀ i, MixedCarrier Z (n+1) (I i)) (B : ∀ j, MixedCarrier Z (n+1) (J j))
    (defA : ∀ i, SortedDefinableOver 𝓜 S.carrier (A i)) (defB : ∀ j, SortedDefinableOver 𝓜 S.carrier (B j))
    (finiteA : ∀ i, HasFiniteFieldFibers (A i)) (finiteB : ∀ j, HasFiniteFieldFibers (B j))
    (iso : (taggedMixedCarriers S I A defA).Iso (taggedMixedCarriers S J B defB)) :
    (∑ i, mixedContractionValue S neg head (A i) (defA i) (finiteA i)) =
      ∑ j, mixedContractionValue S neg head (B j) (defB j) (finiteB j) := by
  let U := taggedMixedCarriers S I A defA
  let V := taggedMixedCarriers S J B defB
  obtain ⟨f,df⟩ := iso
  let D (i : Fin p) (j : Fin q) : MixedCarrier Z (n+1) (I i) := U.sourceCut V f i j
  let E₀ (i : Fin p) (j : Fin q) : MixedCarrier Z (n+1) (J j) := U.targetCut V f i j
  let subD (i : Fin p) (j : Fin q) : D i j ⊆ A i := U.sourceCut_subset V f i j
  let subE (i : Fin p) (j : Fin q) : E₀ i j ⊆ B j := U.targetCut_subset V f i j
  let dD (i : Fin p) (j : Fin q) : SortedDefinableOver 𝓜 S.carrier (D i j) := U.sourceCut_definable V f df i j
  let dE (i : Fin p) (j : Fin q) : SortedDefinableOver 𝓜 S.carrier (E₀ i j) := U.targetCut_definable V f df i j
  let VD (i : Fin p) (j : Fin q) : (Q).Quotient :=
    mixedContractionValue S neg head (D i j) (dD i j) ((finiteA i).mono (subD i j))
  let VE (i : Fin p) (j : Fin q) : (Q).Quotient :=
    mixedContractionValue S neg head (E₀ i j) (dE i j) ((finiteB j).mono (subE i j))
  have rows (i : Fin p) :
      mixedContractionValue S neg head (A i) (defA i) (finiteA i) = ∑ j, VD i j := by
    obtain ⟨disj,cover⟩ := U.sourceCut_partition V f i
    exact mixedContractionValue_partition S neg hyp head (A i) (defA i) (finiteA i)
      (D i) (dD i) (subD i) disj cover
  have cols (j : Fin q) :
      mixedContractionValue S neg head (B j) (defB j) (finiteB j) = ∑ i, VE i j := by
    obtain ⟨disj,cover⟩ := U.targetCut_partition V f j
    exact mixedContractionValue_partition S neg hyp head (B j) (defB j) (finiteB j)
      (fun i => E₀ i j) (fun i => dE i j) (fun i => subE i j) disj cover
  have each (i : Fin p) (j : Fin q) : VD i j = VE i j := by
    obtain ⟨g⟩ := U.cuts_iso V f df i j
    exact mixedContractionValue_of_iso S neg hyp head pair recovery he small basePoint
      g (dD i j) (dE i j) ((finiteA i).mono (subD i j)) ((finiteB j).mono (subE i j))
  calc
    _ = ∑ i, ∑ j, VD i j := Finset.sum_congr rfl (fun i _ => rows i)
    _ = ∑ i, ∑ j, VE i j := Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => each i j))
    _ = ∑ j, ∑ i, VE i j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => (cols j).symm)

end GeneralizedEuler.Section5
