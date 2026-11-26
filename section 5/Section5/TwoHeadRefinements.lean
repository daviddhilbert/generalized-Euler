module

public import Section5.FirstTwoOrderReduction
public import Section5.RelativelyUnaryContractions
public import Section5.StandardHeadContractions

/-! In each order a relatively unary change can be made immediately
before each head. This permits cell-dependent translations without
changing the standard head preparation or the selected old tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {k : ℕ}

structure TwoHeadRefinement (A : RetainedFieldFamily M S 2 k) where
  positioned : RetainedFieldFamily M S 2 k
  first : HeadContractionData (n := 1) positioned
  centered : RetainedFieldFamily M S 1 (k+1)
  second : HeadContractionData (n := 0) centered
  firstIso : MixedGraphIso M S
    {x : SortedAssignment (CanonicalSort O) (MixedVariables 2 A.tags) | mixedTuple x ∈ A.carrier}
    {y : SortedAssignment (CanonicalSort O) (MixedVariables 2 positioned.tags) | mixedTuple y ∈ positioned.carrier}
  firstTail : ∀ x, (firstIso.equiv x).val .vf ∘ Fin.succ = x.val .vf ∘ Fin.succ
  firstSelected : ∀ x, (firstIso.equiv x).val .rv ∘ positioned.select = x.val .rv ∘ A.select
  secondIso : MixedGraphIso M S
    {x : SortedAssignment (CanonicalSort O) (MixedVariables 1 first.target.tags) | mixedTuple x ∈ first.target.carrier}
    {y : SortedAssignment (CanonicalSort O) (MixedVariables 1 centered.tags) | mixedTuple y ∈ centered.carrier}
  secondSelected : ∀ x, (secondIso.equiv x).val .rv ∘ centered.select = x.val .rv ∘ first.target.select
  arity : ℕ
  enumerate : Fin arity ≃ second.target.tags

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (T : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ T.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem TwoHeadRefinement.compare
    (hyp : FieldwiseContractionHypotheses T) (head : HeadPreparationHypotheses O hO power T)
    {A : RetainedFieldFamily 𝓜 T 2 k} (R : TwoHeadRefinement A)
    {U : RetainedFieldFamily 𝓜 T 0 (k+2)} (run : HeadContractionRun A U)
    {a : ℕ} (idx : Fin a ≃ U.tags) :
    terminalCommonBlowup T neg U R.second.target idx R.enumerate := by
  cases run with
  | next H tail =>
    cases tail with
    | next J rest =>
      cases rest
      let : Finite H.target.tags := H.target.finiteTags
      let : Finite R.first.target.tags := R.first.target.finiteTags
      let x : Fin (Nat.card H.target.tags) ≃ H.target.tags := (Finite.equivFin _).symm
      let y : Fin (Nat.card R.first.target.tags) ≃ R.first.target.tags := (Finite.equivFin _).symm
      obtain ⟨G⟩ := head_contraction_data_exists hO power T
        head.minusOne head.minusOne_realizes head.fieldTerms head.fieldTerms_realize R.first.target
        (head.saturated 0 _ R.first.target.finiteTags) (head.immediate 0)
      let : Finite G.target.tags := G.target.finiteTags
      let atom := commonBlowup_equivalence (ElementaryClassStep O hO power T neg)
        (fun {_ _ _} => elementaryClassStep_diamond O hO power T neg)
      let g : Fin (Nat.card G.target.tags) ≃ G.target.tags := (Finite.equivFin _).symm
      have a := relativelyUnary_headTarget_commonBlowup T neg hyp H R.first x y R.firstIso R.firstTail R.firstSelected
      have b := fieldwise_contraction_runs_common_blowup T neg hyp
        (.next J (.done J.target)) (.next G (.done G.target)) x y idx g a
      have c := relativelyUnary_contraction_runs_commonBlowup T neg hyp G R.second g R.enumerate
        (.done G.target) (.done R.second.target) g R.enumerate R.secondIso
        (fun _ => Subsingleton.elim _ _) R.secondSelected
      exact atom.trans b c

theorem two_coordinate_order_comparison_of_refinements
    (hyp : FieldwiseContractionHypotheses T)
    (head : HeadPreparationHypotheses O hO power T)
    (refinement : ∀ A : RetainedFieldFamily 𝓜 T 2 k,
      ∃ (C : TwoHeadRefinement A) (D : TwoHeadRefinement (A.permuteVF (Equiv.swap 0 1))),
        C.second.target.terminalGradedClass C.enumerate (baseRVZero T) rfl =
        D.second.target.terminalGradedClass D.enumerate (baseRVZero T) rfl) :
    TwoCoordinateOrderComparison T neg k := by
  intro a b A U V runU runV idx idy
  obtain ⟨C,D,eq⟩ := refinement A
  have left := C.compare T neg hyp head runU idx
  have right := D.compare T neg hyp head runV idy
  unfold terminalCommonBlowup at left right ⊢
  rw [eq] at left
  let atom := commonBlowup_equivalence (ElementaryClassStep O hO power T neg)
    (fun {_ _ _} => elementaryClassStep_diamond O hO power T neg)
  exact atom.trans left (atom.symm right)

end Canonical

end GeneralizedEuler.Section5
