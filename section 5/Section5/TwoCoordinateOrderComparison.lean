module

public import Section5.PositionedAnnotationsFromHeads
public import Section5.PositionedFamilyOrderComparison
public import Section5.PositioningChartHypotheses

/-! Prepare and record the vertical positions, then use the uniform
unary charts in the other coordinate. This gives the two-coordinate
exchange for arbitrary actual contraction runs. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem two_coordinate_order_comparison
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (chart : PositioningChartHypotheses S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (zero : S.carrier .vf) (hz : zero.val = 0) :
    TwoCoordinateOrderComparison S neg k := by
  intro a b A U V left right iu iv
  let swap := Equiv.swap (0 : Fin 2) 1
  let A' := A.permuteVF swap
  obtain ⟨H⟩ := head_contraction_data_exists hO power S head.minusOne head.minusOne_realizes
    head.fieldTerms head.fieldTerms_realize A' (head.saturated 1 A'.tags A'.finiteTags) (head.immediate 1)
  have annot := positioned_annotation_from_head S head zero A' H
  have eq : (A'.permuteVF swap) = A := by
    change (A.permuteVF swap).permuteVF swap = A
    rw [A.permuteVF_comp]
    rw [show swap.trans swap = Equiv.refl _ from Equiv.swap_swap _ _,A.permuteVF_refl]
  change ∃ (B : RetainedFieldFamily 𝓜 S 2 k) (_ : TaggedPositioningData B)
    (e : MixedGraphIso 𝓜 S
      {a : SortedAssignment (CanonicalSort O) (MixedVariables 2 (A'.permuteVF swap).tags) |
        mixedTuple a ∈ (A'.permuteVF swap).carrier}
      {b : SortedAssignment (CanonicalSort O) (MixedVariables 2 B.tags) | mixedTuple b ∈ B.carrier}),
    (∀ a, (e.equiv a).val .vf = a.val .vf) ∧
    (∀ a, (e.equiv a).val .rv ∘ B.select = a.val .rv ∘ (A'.permuteVF swap).select) at annot
  rw [eq] at annot
  obtain ⟨B,C,e,fix,keep⟩ := annot
  apply two_coordinate_comparison_of_field_fixed_annotation S neg hyp head A B e fix keep ?_ U V iu iv left right
  intro _ _ W X w x iw ix
  exact positioned_family_compare_runs S neg hyp head he small zero hz B C
    (chart.saturatedRV B.tags B.finiteTags) chart.saturatedCenters chart.immediate
    (C.leaf_scheme_exists S head chart he small) w x iw ix

end GeneralizedEuler.Section5
