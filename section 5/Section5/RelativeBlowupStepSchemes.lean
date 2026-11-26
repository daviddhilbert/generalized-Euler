module

public import Section5.RelativeObjectFamilies
public import Section5.RelativeElementaryNaming

/-! A local class step can be named with two graded isomorphism
matrices, one elementary center, and its unchanged family of rows. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder RelativeObjectFamily

universe z

set_option autoImplicit false

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  {P : TCsort → Type} {I J : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

structure RelativeBlowupRecipe
    (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) (P : TCsort → Type) where
  degree : ℕ
  center : RelativeElementaryScheme 𝓜 S P degree
  restCount : ℕ
  rest : RelativeObjectFamily 𝓜 S P (Fin restCount)

namespace RelativeBlowupRecipe

variable (R : RelativeBlowupRecipe S P) (neg : rv O (-1) ∈ S.carrier .rv)

@[expose] def before : RelativeObjectFamily 𝓜 S P (Unit ⊕ Fin R.restCount) :=
  Sum.elim (fun _ => RelativeRVObjectScheme.ofElementary R.center) R.rest

@[expose] def after : RelativeObjectFamily 𝓜 S P (Bool ⊕ Fin R.restCount) :=
  Sum.elim (fun b => match b with
    | false => RelativeRVObjectScheme.ofElementaryLower R.center
    | true => RelativeRVObjectScheme.ofElementaryUpper O hO power S neg R.center) R.rest

@[expose] def valid (zero : S.carrier .rv) (p : SortedAssignment Z P) : Prop :=
  R.center.valid zero p ∧ Valid R.rest zero p

theorem valid_definable (zero : S.carrier .rv) :
    SortedDefinableOver 𝓜 S.carrier {p | R.valid zero p} :=
  (R.center.valid_definable zero).inter (RelativeObjectFamily.valid_definable R.rest zero)

theorem valid_before (R : RelativeBlowupRecipe (L := L) (O := O) (hO := hO) (power := power) S P)
    {zero : S.carrier .rv} {p : SortedAssignment (CanonicalSort O) P}
    (v : R.valid zero p) (i : Unit ⊕ Fin R.restCount) : (R.before i).valid zero p := by
  cases i with
  | inl => exact v.1.1
  | inr j => exact v.2 j

theorem valid_after (R : RelativeBlowupRecipe (L := L) (O := O) (hO := hO) (power := power) S P)
    {zero : S.carrier .rv} {p : SortedAssignment (CanonicalSort O) P}
    (hz : zero.val = 0) (v : R.valid zero p) (i : Bool ⊕ Fin R.restCount) : ((R.after neg) i).valid zero p := by
  cases i with
  | inl b =>
    cases b
    · exact v.1.2
    · exact RelativeRVObjectScheme.ofElementaryUpper_valid O hO power S neg R.center zero hz p v.1
  | inr j => exact v.2 j

end RelativeBlowupRecipe

inductive RelativeBlowupStepScheme
    (neg : rv O (-1) ∈ S.carrier .rv)
    (A : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P I)
    (B : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P J) : Type z where
  | iso (w : IsoScheme A B) : RelativeBlowupStepScheme neg A B
  | elementary (R : RelativeBlowupRecipe S P) (left : IsoScheme A R.before) (right : IsoScheme (R.after neg) B) :
      RelativeBlowupStepScheme neg A B

namespace RelativeBlowupStepScheme

variable {neg : rv O (-1) ∈ S.carrier .rv}
  {A : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P I}
  {B : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P J}

@[expose] def valid (W : RelativeBlowupStepScheme neg A B) (zero : S.carrier .rv) (p : SortedAssignment Z P) : Prop :=
  match W with
  | .iso w => w.valid p
  | .elementary R left right => R.valid zero p ∧ left.valid p ∧ right.valid p

theorem valid_definable [Finite I] [Finite J] (W : RelativeBlowupStepScheme neg A B) (zero : S.carrier .rv) :
    SortedDefinableOver 𝓜 S.carrier {p | W.valid zero p} := by
  cases W with
  | iso w => exact w.valid_definable
  | elementary R left right =>
    exact (R.valid_definable zero).inter (left.valid_definable.inter right.valid_definable)

end RelativeBlowupStepScheme

set_option maxHeartbeats 600000 in
theorem relative_blowup_step_scheme_of_class_step [Fintype I] [Fintype J]
    (neg : rv O (-1) ∈ S.carrier .rv)
    (A : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P I)
    (B : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P J)
    (zero : S.carrier .rv) (hz : zero.val = 0) (p : SortedAssignment Z P)
    (vA : Valid A zero p) (vB : Valid B zero p)
    (sat : ∀ d, let T := (𝓜).termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin d)))
        (BaseAssignments T.carrier (RVVariables (Fin d))))
    (step : let T := (𝓜).termGenerated (namedTuple S p)
      let n : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
      ElementaryClassStep O hO power T n (fiberClass A zero hz p vA) (fiberClass B zero hz p vB)) :
    ∃ W : RelativeBlowupStepScheme neg A B, W.valid zero p := by
  classical
  let T := (𝓜).termGenerated (namedTuple S p)
  let n : rv O (-1) ∈ T.carrier .rv :=
    ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
  rcases step with eq | ⟨U,r,first,second⟩
  · obtain ⟨w,v⟩ := isoScheme_of_fiberClass_eq A B zero hz p vA vB eq
    exact ⟨.iso w,v⟩
  · obtain ⟨C,vC,old,new⟩ := relative_elementary_scheme_of_center O hO power S neg p zero hz U sat
    obtain ⟨m,rest,vRest,restClass⟩ := positive_class_has_named_family zero hz p sat r
    let R : RelativeBlowupRecipe S P := ⟨U.1,C,m,rest⟩
    have vR : R.valid zero p := ⟨vC,vRest⟩
    have eq₁ : fiberClass A zero hz p vA = fiberClass R.before zero hz p (R.valid_before vR) := by
      rw [first,← old,← restClass]
      unfold fiberClass
      rw [Fintype.sum_sum_type]
      simp only [RelativeBlowupRecipe.before,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique]
      rfl
    have eq₂ : fiberClass (R.after neg) zero hz p (R.valid_after neg hz vR) = fiberClass B zero hz p vB := by
      rw [second,← new,← restClass]
      unfold fiberClass
      rw [Fintype.sum_sum_type,Fintype.sum_bool]
      exact congrArg (· + fiberClass rest zero hz p vRest) (add_comm _ _)
    obtain ⟨left,hLeft⟩ := isoScheme_of_fiberClass_eq A R.before zero hz p vA (R.valid_before vR) eq₁
    obtain ⟨right,hRight⟩ := isoScheme_of_fiberClass_eq (R.after neg) B zero hz p (R.valid_after neg hz vR) vB eq₂
    exact ⟨.elementary R left right,vR,hLeft,hRight⟩

end GeneralizedEuler.Section5
