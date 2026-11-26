module

public import Section5.RelativeBlowupPathSchemes
public import Section5.RelativeBlowupStepDescent

/-! Descent of an entire common-blowup witness requires only the finite
list of tag and graph tests on its two paths. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder RelativeObjectFamily RelativeRVTest

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  {neg : rv O (-1) ∈ S.carrier .rv}
  {P Q : TCsort → Type} [Finite (P .vf)] [Finite (P .rv)] {a b : ℕ}
  {A : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P (Fin a)}
  {B : RelativeObjectFamily (canonicalStructure (L := L) O hO power) S P (Fin b)}
  {H : SortedAssignment (CanonicalSort O) P → SortedAssignment (CanonicalSort O) Q → Prop}
  (defH : DefinableRelation (canonicalStructure (L := L) O hO power) S.carrier H)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

namespace RelativeBlowupPath

@[expose] def descend (W : RelativeBlowupPath neg A B) :
    RelativeBlowupPath neg (fun i => (A i).descend defH) (fun j => (B j).descend defH) := by
  induction W with
  | refl A => exact .refl (fun i => (A i).descend defH)
  | cons C head _ ih => exact .cons (fun i => (C i).descend defH) (head.descend defH) ih

omit [Finite (P .vf)] [Finite (P .rv)] in
@[expose] def tests (W : RelativeBlowupPath neg A B) : List (RelativeRVTest 𝓜 S P) := by
  induction W with
  | refl A => exact RelativeObjectFamily.tests A
  | @cons a m b A C B head tail ih => exact RelativeObjectFamily.tests A ++ head.tests ++ ih

theorem descend_valid_of_tests (W : RelativeBlowupPath neg A B)
    {p : SortedAssignment Z P} {q : SortedAssignment Z Q} (hp : H p q)
    (agree : ∀ p', H p' q → Agree W.tests p p') (zero : S.carrier .rv)
    (v : W.valid zero p) : (W.descend defH).valid zero q := by
  induction W with
  | refl A => exact RelativeObjectFamily.descend_valid_of_tests A defH hp agree zero v
  | @cons a m b A C B head tail ih =>
    have first p' h' := (agree_append.1 (agree p' h')).1
    have last p' h' := (agree_append.1 (agree p' h')).2
    exact ⟨RelativeObjectFamily.descend_valid_of_tests A defH hp (fun p' h' => (agree_append.1 (first p' h')).1) zero v.1,
      head.descend_valid_of_tests defH hp (fun p' h' => (agree_append.1 (first p' h')).2) zero v.2.1,
      ih last v.2.2⟩

end RelativeBlowupPath

namespace RelativeCommonBlowupScheme

@[expose] def descend (W : RelativeCommonBlowupScheme neg A B) :
    RelativeCommonBlowupScheme neg (fun i => (A i).descend defH) (fun j => (B j).descend defH) :=
  ⟨W.count,fun i => (W.target i).descend defH,W.left.descend defH,W.right.descend defH⟩

omit [Finite (P .vf)] [Finite (P .rv)] in
@[expose] def tests (W : RelativeCommonBlowupScheme neg A B) : List (RelativeRVTest 𝓜 S P) :=
  W.left.tests ++ W.right.tests

theorem descend_valid_of_tests (W : RelativeCommonBlowupScheme neg A B)
    {p : SortedAssignment Z P} {q : SortedAssignment Z Q} (hp : H p q)
    (agree : ∀ p', H p' q → Agree W.tests p p') (zero : S.carrier .rv)
    (v : W.valid zero p) : (W.descend defH).valid zero q :=
  ⟨W.left.descend_valid_of_tests defH hp (fun p' h' => (agree_append.1 (agree p' h')).1) zero v.1,
    W.right.descend_valid_of_tests defH hp (fun p' h' => (agree_append.1 (agree p' h')).2) zero v.2⟩

end RelativeCommonBlowupScheme

end GeneralizedEuler.Section5
