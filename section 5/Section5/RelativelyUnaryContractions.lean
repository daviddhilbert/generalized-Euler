module

public import Section5.FieldwiseContractionInduction
public import Section5.TailFieldBijections

/-! Contracting a relatively unary coordinate first gives pointwise
common blowups of the remaining families. Continuing in the same
order preserves the terminal class modulo common blowups. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

variable (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)
  {n k a b c d l : ℕ}

set_option maxHeartbeats 900000 in
theorem relativelyUnary_headTarget_commonBlowup
    (hyp : FieldwiseContractionHypotheses S)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k} (H : HeadContractionData A) (J : HeadContractionData B)
    (idxH : Fin a ≃ H.target.tags) (idxJ : Fin b ≃ J.target.tags)
    (f : MixedGraphIso 𝓜 S
      {x : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple x ∈ A.carrier}
      {y : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple y ∈ B.carrier})
    (fixTail : ∀ x, (f.equiv x).val .vf ∘ Fin.succ = x.val .vf ∘ Fin.succ)
    (fixSelected : ∀ x, (f.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select) :
    fieldwiseCommonBlowup S neg H.target J.target idxH idxJ := by
  intro p
  let T := (𝓜).termGenerated (namedTuple S p)
  let nt : rv O (-1) ∈ T.carrier .rv :=
    ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
  let C := A.fieldTailSlice p
  let D := B.fieldTailSlice p
  let HC := H.atFieldTail p
  let JD := J.atFieldTail p
  obtain ⟨g,keep⟩ := A.fieldTailSlices_iso B f fixTail fixSelected p
  have h : terminalCommonBlowup T nt HC.target JD.target idxH idxJ :=
    unary_head_terminal_classes_common_blowup_of_iso hO power T HC JD (hyp.head n p k C D HC JD) nt
      (baseRVZero T) rfl idxH idxJ g keep
  exact headTarget_terminalCommonBlowup_of_tail S neg H J idxH idxJ p h

theorem relativelyUnary_contraction_runs_commonBlowup
    (hyp : FieldwiseContractionHypotheses S)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k} (H : HeadContractionData A) (J : HeadContractionData B)
    (idxH : Fin a ≃ H.target.tags) (idxJ : Fin b ≃ J.target.tags)
    {U V : RetainedFieldFamily 𝓜 S 0 l}
    (runH : HeadContractionRun H.target U) (runJ : HeadContractionRun J.target V)
    (idxU : Fin c ≃ U.tags) (idxV : Fin d ≃ V.tags)
    (f : MixedGraphIso 𝓜 S
      {x : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple x ∈ A.carrier}
      {y : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple y ∈ B.carrier})
    (fixTail : ∀ x, (f.equiv x).val .vf ∘ Fin.succ = x.val .vf ∘ Fin.succ)
    (fixSelected : ∀ x, (f.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select) :
    terminalCommonBlowup S neg U V idxU idxV :=
  fieldwise_contraction_runs_common_blowup S neg hyp runH runJ idxH idxJ idxU idxV
    (relativelyUnary_headTarget_commonBlowup S neg hyp H J idxH idxJ f fixTail fixSelected)

end GeneralizedEuler.Section5
