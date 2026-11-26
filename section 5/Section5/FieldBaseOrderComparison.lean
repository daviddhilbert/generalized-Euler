module

public import Section5.TwoCoordinateOrderComparison
public import Section5.StandardOrderComparison

/-! Apply the two-coordinate exchange over each field-generated base
used by induction on the order of contraction. -/

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

theorem two_coordinate_comparison_at_field_bases
    (hyp : ∀ n (p : fieldAssignment n Z), FieldwiseContractionHypotheses ((𝓜).termGenerated (namedTuple S p)))
    (head : ∀ n (p : fieldAssignment n Z), HeadPreparationHypotheses O hO power ((𝓜).termGenerated (namedTuple S p)))
    (chart : ∀ n (p : fieldAssignment n Z), PositioningChartHypotheses ((𝓜).termGenerated (namedTuple S p)))
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (zero : S.carrier .vf) (hz : zero.val = 0) :
    TwoCoordinateComparisonAtFieldBases S neg := by
  intro n k p arityLeft arityRight A U V left right iu iv
  let a := (𝓜).termGeneratedAssignment (namedTuple S p)
  exact (two_coordinate_order_comparison (k := k) _ (a .rv (.inl ⟨_,neg⟩)).property
    (hyp n p) (head n p) (chart n p) he small (a .vf (.inl zero)) hz)
    A U V left right iu iv

end GeneralizedEuler.Section5
