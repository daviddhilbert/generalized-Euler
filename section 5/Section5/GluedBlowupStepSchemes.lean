module

public import Section5.RelativeBlowupStepSchemes
public import Section5.RelativeElementaryRows

/-! Each named local step glues to an elementary class step with the
same retained head start, even when the end families change arity. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder RelativeObjectFamily

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  (neg : rv O (-1) ∈ S.carrier .rv) {h t : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Q" => RVVariables (Fin h)

variable (D : RelativeRVIndex (X := CanonicalSort O) (canonicalStructure (L := L) O hO power) S h t)
  (zero : S.carrier .rv) (hz : zero.val = 0)

theorem RelativeBlowupRecipe.glued_step (R : RelativeBlowupRecipe S Q)
    (v : ∀ p ∈ D.labels, R.valid zero (rvTupleAssignment p)) :
    ElementaryClassStep O hO power S neg
      (gluedClass zero hz D R.before (fun p hp => R.valid_before (v p hp)))
      (gluedClass zero hz D (R.after neg) (fun p hp => R.valid_after neg hz (v p hp))) := by
  let centerValid p hp := (v p hp).1
  let A := R.center.row D zero hz centerValid
  let f := R.center.row_deleted_bound D zero hz centerValid
  let B := A.lowerRow R.center.slot f
  let C := RelativeRVRow.upperRow O hO power S neg A R.center.slot f
  let rest := gluedClass zero hz D R.rest (fun p hp => (v p hp).2)
  have geom : ElementaryClassStep O hO power S neg A.gluedClass (B.gluedClass+C.gluedClass) :=
    relative_elementary_scheme_glued_step O hO power S neg R.center D zero hz centerValid
  have s := elementaryClassStep_add O hO power S neg geom rest
  have oldClass : gluedClass zero hz D R.before (fun p hp => R.valid_before (v p hp)) = A.gluedClass+rest := by
    unfold gluedClass
    rw [Fintype.sum_sum_type,Fintype.sum_unique]
    rfl
  have newClass : gluedClass zero hz D (R.after neg) (fun p hp => R.valid_after neg hz (v p hp)) =
      B.gluedClass+C.gluedClass+rest := by
    unfold gluedClass
    rw [Fintype.sum_sum_type,Fintype.sum_bool]
    exact congrArg (· + rest) (add_comm _ _)
  rw [oldClass,newClass]
  exact s

theorem RelativeBlowupStepScheme.glued_step {I J : Type} [Fintype I] [Fintype J]
    {A : RelativeObjectFamily 𝓜 S Q I} {B : RelativeObjectFamily 𝓜 S Q J}
    (W : RelativeBlowupStepScheme neg A B)
    (vA : ∀ p ∈ D.labels, Valid A zero (rvTupleAssignment p))
    (vB : ∀ p ∈ D.labels, Valid B zero (rvTupleAssignment p))
    (v : ∀ p ∈ D.labels, W.valid zero (rvTupleAssignment p)) :
    ElementaryClassStep O hO power S neg (gluedClass zero hz D A vA) (gluedClass zero hz D B vB) := by
  cases W with
  | iso w =>
    exact Or.inl (gluedClass_eq_of_isoScheme zero hz D _ vA vB w v)
  | elementary R left right =>
    let vR p hp := (v p hp).1
    have eA := gluedClass_eq_of_isoScheme zero hz D A vA (fun p hp => R.valid_before (vR p hp)) left
      (fun p hp => (v p hp).2.1)
    have eB := gluedClass_eq_of_isoScheme zero hz D (R.after neg) (fun p hp => R.valid_after neg hz (vR p hp)) vB right
      (fun p hp => (v p hp).2.2)
    rw [eA,← eB]
    exact R.glued_step neg D zero hz vR

end GeneralizedEuler.Section5
