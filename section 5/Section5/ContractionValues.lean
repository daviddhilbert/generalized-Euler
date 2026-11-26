module

public import Section5.ContractionCutClasses
public import Section5.StandardOrderComparison
public import Section5.PaddedLiftIdentityClass

/-! The terminal class modulo common blowups is independent of
preparation, additive on cuts, and invariant under relatively unary
maps when the two-coordinate exchange is available. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n k l a q : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Q" => (gradedBlowupCongruence O hO power S neg)

@[expose] def chosenHeadOutput (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S n k) : StandardHeadOutput A (Equiv.refl _) :=
  Classical.choice (standard_head_output_exists head A (Equiv.refl _))

theorem chosenHeadOutput_run (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S n k) : HeadContractionRun A (chosenHeadOutput S head A).terminal := by
  have run := (chosenHeadOutput S head A).run
  rwa [A.permuteVF_refl] at run

@[expose] def contractionValue (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S n k) : (Q).Quotient :=
  let B := chosenHeadOutput S head A
  ((Q).mk') (B.terminal.terminalGradedClass B.tags (baseRVZero S) rfl)

theorem contractionValue_of_run
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S n k) (B : RetainedFieldFamily 𝓜 S 0 l)
    (run : HeadContractionRun A B) (idx : Fin a ≃ B.tags) :
    contractionValue S neg head A = ((Q).mk') (B.terminalGradedClass idx (baseRVZero S) rfl) := by
  have count := run.selected_count
  subst l
  let U : StandardHeadOutput A (Equiv.refl _) := ⟨B,by rw [A.permuteVF_refl]; exact run,a,idx⟩
  let : Finite A.tags := A.finiteTags
  let ia : Fin (Nat.card A.tags) ≃ A.tags := (Finite.equivFin _).symm
  exact Quotient.sound (same_order_standard_outputs_independent S neg hyp ia (chosenHeadOutput S head A) U)

theorem contractionValue_partition
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (A : RetainedFieldFamily 𝓜 S (n+1) k)
    (D : Fin q → MixedCarrier Z (n+1) A.tags) (d : ∀ i, SortedDefinableOver 𝓜 S.carrier (D i))
    (sub : ∀ i, D i ⊆ {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier})
    (disj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (cover : ∀ a : SortedAssignment Z (MixedVariables (n+1) A.tags), mixedTuple a ∈ A.carrier → ∃ i, a ∈ D i) :
    contractionValue S neg head A =
      ∑ i, contractionValue S neg head (A.cutCarrier (D i) (d i) (sub i)) := by
  let U := chosenHeadOutput S head A
  let V (i : Fin q) := chosenHeadOutput S head (A.cutCarrier (D i) (d i) (sub i))
  exact contraction_class_partition S neg hyp head A D d sub disj cover U.tags
    (chosenHeadOutput_run S head A) (fun i => (V i).terminal)
    (fun i => chosenHeadOutput_run S head (A.cutCarrier (D i) (d i) (sub i)))
    (fun i => (V i).arity) (fun i => (V i).tags)

theorem contractionValue_of_field_fixed
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k}
    (f : MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier})
    (fix : ∀ a, (f.equiv a).val .vf = a.val .vf)
    (keep : ∀ a, (f.equiv a).val .rv ∘ B.select = a.val .rv ∘ A.select) :
    contractionValue S neg head A = contractionValue S neg head B := by
  let U := chosenHeadOutput S head A
  let V := chosenHeadOutput S head B
  exact Quotient.sound (contraction_runs_commonBlowup_of_field_fixed S neg hyp f fix keep U.tags V.tags
    (chosenHeadOutput_run S head A) (chosenHeadOutput_run S head B))

theorem contractionValue_of_relatively_unary
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k}
    (f : MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier})
    (i : Fin (n+1))
    (fix : ∀ a j, j ≠ i → (f.equiv a).val .vf j = a.val .vf j)
    (keep : ∀ a, (f.equiv a).val .rv ∘ B.select = a.val .rv ∘ A.select) :
    contractionValue S neg head A = contractionValue S neg head B :=
  Quotient.sound (relativelyUnary_outputs_of_arbitrary_orders S neg hyp head pair
    (chosenHeadOutput S head A) (chosenHeadOutput S head B) f i fix keep)

theorem contractionValue_padded_lift
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    {d : ℕ} (U : RVObject 𝓜 S d) (p : Fin d ↪ Fin n) :
    contractionValue S neg head (paddedLiftFamily O hO power S U p) = ((Q).mk') (objectClass 𝓜 S ⟨d,U⟩) := by
  obtain ⟨B,a,idx,run,eq⟩ := padded_lift_identity_class O hO power S head.fieldTerms
    head.minusOne head.minusOne_realizes head.fieldTerms_realize zero hz U p
  exact (contractionValue_of_run S neg hyp head _ B run idx).trans (congrArg ((Q).mk') eq)

end GeneralizedEuler.Section5
