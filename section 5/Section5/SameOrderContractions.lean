module

public import Section5.RelativelyUnaryContractions
public import Section5.StandardHeadContractions

/-! The fieldwise comparison applies to any prescribed common order.
In particular, changing the head preparations in that order
preserves the terminal class modulo common blowups. -/

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
  {n k a b : ℕ}

theorem fieldwiseCommonBlowup_permute
    {A B : RetainedFieldFamily 𝓜 S n k} (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags)
    (order : Equiv.Perm (Fin n)) (h : fieldwiseCommonBlowup S neg A B idxA idxB) :
    fieldwiseCommonBlowup S neg (A.permuteVF order) (B.permuteVF order) idxA idxB := by
  intro p
  let p' : fieldAssignment n Z := fieldTupleAssignment (p .vf ∘ order.symm)
  let T := (𝓜).termGenerated (namedTuple S p)
  let T' := (𝓜).termGenerated (namedTuple S p')
  let nt : rv O (-1) ∈ T.carrier .rv :=
    ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
  let nt' : rv O (-1) ∈ T'.carrier .rv :=
    ((𝓜).termGeneratedAssignment (namedTuple S p') .rv (.inl ⟨_,neg⟩)).property
  have eq : T' = T := generated_base_field_perm S p order.symm
  have c := terminalCommonBlowup_rebase T' nt' eq nt (A.atFieldTuple p') (B.atFieldTuple p') idxA idxB (h p')
  exact terminalCommonBlowup_of_carriers T nt rfl rfl rfl rfl c

theorem same_order_standard_outputs_commonBlowup
    (hyp : FieldwiseContractionHypotheses S)
    {A B : RetainedFieldFamily 𝓜 S n k} (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags)
    {order : Equiv.Perm (Fin n)} (U : StandardHeadOutput A order) (V : StandardHeadOutput B order)
    (h : fieldwiseCommonBlowup S neg A B idxA idxB) :
    terminalCommonBlowup S neg U.terminal V.terminal U.tags V.tags :=
  fieldwise_contraction_runs_common_blowup S neg hyp U.run V.run idxA idxB U.tags V.tags
    (fieldwiseCommonBlowup_permute S neg idxA idxB order h)

theorem same_order_standard_outputs_independent
    (hyp : FieldwiseContractionHypotheses S)
    {A : RetainedFieldFamily 𝓜 S n k} (idx : Fin a ≃ A.tags)
    {order : Equiv.Perm (Fin n)} (U V : StandardHeadOutput A order) :
    terminalCommonBlowup S neg U.terminal V.terminal U.tags V.tags := by
  apply same_order_standard_outputs_commonBlowup S neg hyp idx idx U V
  intro p
  exact ⟨_,0,0,rfl,rfl⟩

end GeneralizedEuler.Section5
