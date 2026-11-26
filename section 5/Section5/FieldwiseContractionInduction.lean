module

public import Section5.FieldwiseTailComparison
public import Section5.HeadContractionIteration
public import Section5.TerminalTagReindexing

/-! The pointwise common-blowup relation passes through corresponding
head steps and therefore through a contraction run. At each step
the new leading term joins the head start. -/

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

structure FieldwiseContractionHypotheses where
  unary : ∀ n (p : fieldAssignment n Z), UnaryFieldwiseHypotheses O hO power ((𝓜).termGenerated (namedTuple S p))
  head : ∀ n (p : fieldAssignment n Z) k,
    let T := (𝓜).termGenerated (namedTuple S p)
    ∀ (A B : RetainedFieldFamily 𝓜 T 1 k) (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B),
      UnaryHeadComparisonHypotheses O hO power T H J

variable {n k a b c d l : ℕ}

set_option maxHeartbeats 900000 in
theorem headTarget_fieldwiseCommonBlowup
    (hyp : FieldwiseContractionHypotheses S)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k} {idxA : Fin a ≃ A.tags} {idxB : Fin b ≃ B.tags}
    (H : HeadContractionData A) (J : HeadContractionData B)
    (idxH : Fin c ≃ H.target.tags) (idxJ : Fin d ≃ J.target.tags)
    (common : fieldwiseCommonBlowup S neg A B idxA idxB) :
    fieldwiseCommonBlowup S neg H.target J.target idxH idxJ := by
  intro p
  let T := (𝓜).termGenerated (namedTuple S p)
  let nt : rv O (-1) ∈ T.carrier .rv :=
    ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
  let C := A.fieldTailSlice p
  let D := B.fieldTailSlice p
  let HC := H.atFieldTail p
  let JD := J.atFieldTail p
  have each := fieldwiseCommonBlowup_tail S neg common p
  have all : SortedDefinableOver 𝓜 T.carrier (Set.univ : Set (fieldAssignment 1 Z)) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  have h : terminalCommonBlowup T nt HC.target JD.target idxH idxJ := by
    apply unary_fieldwise_common_blowup O hO power T (hyp.unary n p) nt (baseRVZero T) rfl C D idxA idxB HC JD idxH idxJ
      (fun g => hyp.head n p k C C HC g) (fun g => hyp.head n p k D D JD g) Set.univ all
      (fun p _ _ => Set.mem_univ p) (fun p _ _ => Set.mem_univ p)
    intro q _
    exact each q
  exact headTarget_terminalCommonBlowup_of_tail S neg H J idxH idxJ p h

set_option maxHeartbeats 900000 in
theorem fieldwise_contraction_runs_common_blowup
    (hyp : FieldwiseContractionHypotheses S)
    {A B : RetainedFieldFamily 𝓜 S n k} {U V : RetainedFieldFamily 𝓜 S 0 l}
    (runA : HeadContractionRun A U) (runB : HeadContractionRun B V)
    (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags)
    (idxU : Fin c ≃ U.tags) (idxV : Fin d ≃ V.tags)
    (common : fieldwiseCommonBlowup S neg A B idxA idxB) :
    terminalCommonBlowup S neg U V idxU idxV := by
  induction runA generalizing a b with
  | done =>
    cases runB
    exact terminalCommonBlowup_reindex S neg idxA idxB idxU idxV (terminalCommonBlowup_of_fieldwise_zero S neg common)
  | next H rest ih =>
    cases runB with
    | next J rest' =>
      let := H.target.finiteTags
      let := J.target.finiteTags
      let fy := Fintype.ofFinite H.target.tags
      let fz := Fintype.ofFinite J.target.tags
      let idxH := (@Fintype.equivFin H.target.tags fy).symm
      let idxJ := (@Fintype.equivFin J.target.tags fz).symm
      have head := headTarget_fieldwiseCommonBlowup S neg hyp H J idxH idxJ common
      exact ih rest' idxH idxJ idxU idxV head

end GeneralizedEuler.Section5
