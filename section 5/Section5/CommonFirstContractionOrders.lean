module

public import Section5.ContractionTailOrders
public import Section5.SameOrderContractions

/-! When two orders share their first coordinate, use the same
preparation there. Independence of the remaining order then gives
the comparison of all outputs in these two orders. -/

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

@[expose] def ContractionOrderComparisonAt (n : ℕ) : Prop :=
  ∀ {k l a b : ℕ} (A : RetainedFieldFamily 𝓜 S n k) (p : Equiv.Perm (Fin n))
    {U V : RetainedFieldFamily 𝓜 S 0 l}
    (idx : Fin a ≃ U.tags) (idy : Fin b ≃ V.tags),
    HeadContractionRun A U → HeadContractionRun (A.permuteVF p) V →
    terminalCommonBlowup S neg U V idx idy

theorem compare_shared_first_contraction
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    {n k l a b : ℕ} (tailCompare : ContractionOrderComparisonAt S neg n)
    (A : RetainedFieldFamily 𝓜 S (n+1) k) (p : Equiv.Perm (Fin n))
    {U V : RetainedFieldFamily 𝓜 S 0 l} (idx : Fin a ≃ U.tags) (idy : Fin b ≃ V.tags)
    (left : HeadContractionRun A U) (right : HeadContractionRun (A.permuteVF (FinOrder.keepFirst p)) V) :
    terminalCommonBlowup S neg U V idx idy := by
  cases left with
  | next H tail =>
    have count := tail.selected_count
    subst l
    have heads (m k : ℕ) (D : RetainedFieldFamily 𝓜 S (m+1) k) : Nonempty (HeadContractionData D) :=
      head_contraction_data_exists hO power S head.minusOne head.minusOne_realizes head.fieldTerms head.fieldTerms_realize
        D (head.saturated m D.tags D.finiteTags) (head.immediate m)
    obtain ⟨W,rW⟩ := HeadContractionRun.exists_run heads (H.target.permuteVF p)
    let : Finite W.tags := W.finiteTags
    let it : Fin (Nat.card W.tags) ≃ W.tags := (Finite.equivFin _).symm
    have run : HeadContractionRun (A.permuteVF (FinOrder.keepFirst p)) W :=
      .next (H.permuteTail p) (by rw [H.permuteTail_target]; exact rW)
    have inner := tailCompare H.target p idx it tail rW
    let : Finite A.tags := A.finiteTags
    let ia : Fin (Nat.card A.tags) ≃ A.tags := (Finite.equivFin _).symm
    have outer := fieldwise_contraction_runs_common_blowup S neg hyp run right ia ia it idy
      (by intro p; exact ⟨_,0,0,rfl,rfl⟩)
    let eq := commonBlowup_equivalence (ElementaryClassStep O hO power S neg)
      (fun {_ _ _} => elementaryClassStep_diamond O hO power S neg)
    exact eq.trans inner outer

end GeneralizedEuler.Section5
