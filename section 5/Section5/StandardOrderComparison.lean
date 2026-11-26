module

public import Section5.ArbitraryContractionOrders
public import Section5.RelativelyUnaryInAnyOrder

/-! Reindex the two requested orders relative to each other. This
also compares arbitrary outputs along a relatively unary arrow. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem standard_output_order_independent
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg)
    {A : RetainedFieldFamily 𝓜 S n k} {p q : Equiv.Perm (Fin n)}
    (U : StandardHeadOutput A p) (V : StandardHeadOutput A q) :
    terminalCommonBlowup S neg U.terminal V.terminal U.tags V.tags := by
  let r := q.trans p.symm
  have eq : r.trans p = q := Equiv.ext (fun i => p.apply_symm_apply (q i))
  have run : HeadContractionRun ((A.permuteVF p).permuteVF r) V.terminal := by
    rw [A.permuteVF_comp,eq]
    exact V.run
  exact contraction_order_comparison_of_two_coordinates S neg hyp head pair n
    (A.permuteVF p) r U.tags V.tags U.run run

theorem relativelyUnary_outputs_of_arbitrary_orders
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k}
    {p q : Equiv.Perm (Fin (n+1))} (U : StandardHeadOutput A p) (V : StandardHeadOutput B q)
    (f : MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier})
    (i : Fin (n+1))
    (fixed : ∀ x j, j ≠ i → (f.equiv x).val .vf j = x.val .vf j)
    (keep : ∀ x, (f.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select) :
    terminalCommonBlowup S neg U.terminal V.terminal U.tags V.tags := by
  let r := Equiv.swap (0 : Fin (n+1)) i
  have r0 : r 0 = i := Equiv.swap_apply_left _ _
  obtain ⟨W⟩ := standard_head_output_exists head A r
  obtain ⟨T⟩ := standard_head_output_exists head B r
  have a := standard_output_order_independent S neg hyp head pair U W
  have b := relativelyUnary_standard_outputs_commonBlowup S neg hyp W T f (fun x j h => fixed x j (r0 ▸ h)) keep
  have c := standard_output_order_independent S neg hyp head pair T V
  let eq := commonBlowup_equivalence (ElementaryClassStep O hO power S neg)
    (fun {_ _ _} => elementaryClassStep_diamond O hO power S neg)
  exact eq.trans a (eq.trans b c)

end GeneralizedEuler.Section5
