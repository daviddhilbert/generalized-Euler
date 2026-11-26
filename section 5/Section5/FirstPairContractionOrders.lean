module

public import Section5.CommonFirstContractionOrders
public import Section5.FirstTwoOrderReduction

/-! A local two-coordinate comparison over every named complementary
tuple gives comparison of any two runs with the first pair swapped. -/

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

@[expose] def TwoCoordinateComparisonAtFieldBases : Prop :=
  ∀ n k (p : fieldAssignment n Z),
    TwoCoordinateOrderComparison ((𝓜).termGenerated (namedTuple S p))
      (((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property) k

theorem compare_swapped_first_pair
    (hyp : FieldwiseContractionHypotheses S) (pair : TwoCoordinateComparisonAtFieldBases S neg)
    {n k l a b : ℕ} (A : RetainedFieldFamily 𝓜 S (n+2) k)
    {U V : RetainedFieldFamily 𝓜 S 0 l} (idx : Fin a ≃ U.tags) (idy : Fin b ≃ V.tags)
    (left : HeadContractionRun A U) (right : HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V) :
    terminalCommonBlowup S neg U V idx idy := by
  cases left with
  | next H tailU =>
    cases tailU with
    | next J tailL =>
      cases right with
      | next H' tailV =>
        cases tailV with
        | next J' tailR =>
          let : Finite J.target.tags := J.target.finiteTags
          let : Finite J'.target.tags := J'.target.finiteTags
          let j : Fin (Nat.card J.target.tags) ≃ J.target.tags := (Finite.equivFin _).symm
          let j' : Fin (Nat.card J'.target.tags) ≃ J'.target.tags := (Finite.equivFin _).symm
          exact first_two_exchange_with_tail S neg hyp A H J H' J' j j' U V tailL tailR idx idy (pair n k)

end GeneralizedEuler.Section5
