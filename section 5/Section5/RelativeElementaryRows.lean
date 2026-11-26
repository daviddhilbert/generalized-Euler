module

public import Section5.RelativeElementaryDescent
public import Section5.RelativeRVBlowupChains

/-! A valid descended elementary scheme supplies a genuine indexed
row with its known finite deletion bound. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {h t k : ℕ}

namespace RelativeElementaryScheme

variable (W : RelativeElementaryScheme M S (RVVariables (Fin h)) k)
  (I : RelativeRVIndex M S h t) (zero : S.carrier .rv)
  (hzero : zero.val = M.funMap .rvZero (fun j => j.elim0))
  (valid : ∀ p ∈ I.labels, W.valid zero (rvTupleAssignment p))

@[expose] def row : RelativeRVRow I (k+1) where
  arity := W.arity
  tags := W.tags
  tagsDefinable := W.tagsDefinable
  graph := W.graph
  graphDefinable := W.graphDefinable
  valid p hp := ⟨W.sourceBound,hzero ▸ (valid p hp).1⟩

theorem row_deleted_bound : (W.row I zero hzero valid).DeletedBound W.slot :=
  fun p hp => ⟨W.deletionBound,hzero ▸ (valid p hp).2⟩

end RelativeElementaryScheme

section Canonical

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S₀.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem relative_elementary_scheme_glued_step
    (W : RelativeElementaryScheme 𝓜 S₀ (RVVariables (Fin h)) k)
    (I : RelativeRVIndex (X := CanonicalSort O) (canonicalStructure (L := L) O hO power) S₀ h t)
    (zero : S₀.carrier .rv) (hzero : zero.val = 0)
    (valid : ∀ p ∈ I.labels, W.valid zero (rvTupleAssignment p)) :
    let A := W.row I zero hzero valid
    let f := W.row_deleted_bound I zero hzero valid
    let B := A.lowerRow W.slot f
    let C := RelativeRVRow.upperRow O hO power S₀ neg A W.slot f
    ElementaryClassStep O hO power S₀ neg A.gluedClass (B.gluedClass + C.gluedClass) := by
  intro A f B C
  apply RelativeRVRow.glued_row_blowup O hO power S₀ neg A W.slot f C
  let D := gluedRVTags I.labels C.tags
  have defD := gluedRVTags_definable I.definable C.tagsDefinable
  change RVDefinablyEquivalent 𝓜 S₀.carrier D D
  exact ⟨Equiv.refl D,definable_identity_label 𝓜 S₀ defD⟩

end Canonical

end GeneralizedEuler.Section5
