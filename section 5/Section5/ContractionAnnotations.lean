module

public import Section5.RelativelyUnaryInAnyOrder
public import Section5.ContractionTailOrders
public import Section5.FirstTwoOrderReduction

/-! Adding a definable annotation that fixes all field coordinates
preserves the two-coordinate comparison in both orders. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {k a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem two_coordinate_comparison_of_field_fixed_annotation
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (A B : RetainedFieldFamily 𝓜 S 2 k)
    (f : MixedGraphIso 𝓜 S
      {x : SortedAssignment Z (MixedVariables 2 A.tags) | mixedTuple x ∈ A.carrier}
      {y : SortedAssignment Z (MixedVariables 2 B.tags) | mixedTuple y ∈ B.carrier})
    (sameField : ∀ x, (f.equiv x).val .vf = x.val .vf)
    (keep : ∀ x, (f.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select)
    (compare : ∀ {c d : ℕ} {W X : RetainedFieldFamily 𝓜 S 0 (k+2)}
      (_ : HeadContractionRun B W) (_ : HeadContractionRun (B.permuteVF (Equiv.swap 0 1)) X)
      (iw : Fin c ≃ W.tags) (ix : Fin d ≃ X.tags), terminalCommonBlowup S neg W X iw ix)
    (U V : RetainedFieldFamily 𝓜 S 0 (k+2)) (iu : Fin a ≃ U.tags) (iv : Fin b ≃ V.tags)
    (u : HeadContractionRun A U) (v : HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V) :
    terminalCommonBlowup S neg U V iu iv := by
  let L : StandardHeadOutput A (Equiv.refl _) := ⟨U,by rw [A.permuteVF_refl]; exact u,a,iu⟩
  let R : StandardHeadOutput A (Equiv.swap 0 1) := ⟨V,v,b,iv⟩
  obtain ⟨P⟩ := standard_head_output_exists head B (Equiv.refl _)
  obtain ⟨Q⟩ := standard_head_output_exists head B (Equiv.swap 0 1)
  have left := relativelyUnary_standard_outputs_commonBlowup S neg hyp L P f
    (fun x i _ => congrFun (sameField x) i) keep
  have right := relativelyUnary_standard_outputs_commonBlowup S neg hyp R Q f
    (fun x i _ => congrFun (sameField x) i) keep
  have runP := P.run
  rw [B.permuteVF_refl] at runP
  have middle := compare runP Q.run P.tags Q.tags
  let eq := commonBlowup_equivalence (ElementaryClassStep O hO power S neg)
    (fun {_ _ _} => elementaryClassStep_diamond O hO power S neg)
  exact eq.trans left (eq.trans middle (eq.symm right))

end GeneralizedEuler.Section5
