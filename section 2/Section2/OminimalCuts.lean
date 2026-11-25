module

public import Section2.PowerBounded

/-! The unary cut calculation used before Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

variable {X Y A : Type*} [LinearOrder X] [LinearOrder Y]

/-- Points and intervals specified by named endpoints in the base. -/
inductive UnaryCellCode (A : Type*)
  | univ
  | point (a : A)
  | below (a : A)
  | above (a : A)
  | between (a b : A)

/-- The realization of a cell in the ambient order containing the base. -/
def UnaryCellCode.asSet (i : A → X) : UnaryCellCode A → Set X
  | .univ => Set.univ
  | .point a => {i a}
  | .below a => Set.Iio (i a)
  | .above a => Set.Ioi (i a)
  | .between a b => Set.Ioo (i a) (i b)

variable {i : A → X} {j : A → Y} {x : X} {y : Y}

/-- Matching cuts transport membership in every interval with endpoints in
the base, and in every singleton named by the base. -/
theorem UnaryCellCode.mem_iff_of_sameCut
    (hcut : ∀ a, (i a < x ↔ j a < y) ∧ (x < i a ↔ y < j a))
    (C : UnaryCellCode A) : x ∈ C.asSet i ↔ y ∈ C.asSet j := by
  cases C with
  | univ => rfl
  | point a =>
    change x = i a ↔ y = j a
    constructor
    · intro h
      exact (not_lt.mp (fun hlt => ((hcut a).1.mpr hlt).ne h.symm)).antisymm
        (not_lt.mp (fun hlt => ((hcut a).2.mpr hlt).ne h))
    · intro h
      exact (not_lt.mp (fun hlt => ((hcut a).1.mp hlt).ne h.symm)).antisymm
        (not_lt.mp (fun hlt => ((hcut a).2.mp hlt).ne h))
  | below a => exact (hcut a).2
  | above a => exact (hcut a).1
  | between a b => exact and_congr (hcut a).1 (hcut b).2

/-- Membership transfers across a finite cell description. The same codes
are used on both sides of the embedding of the base. -/
theorem mem_cellUnion_iff_of_sameCut
    (hcut : ∀ a, (i a < x ↔ j a < y) ∧ (x < i a ↔ y < j a))
    {n : ℕ} (cells : Fin n → UnaryCellCode A) :
    x ∈ (⋃ q, (cells q).asSet i) ↔ y ∈ (⋃ q, (cells q).asSet j) := by
  simpa only [Set.mem_iUnion] using exists_congr (fun q => (cells q).mem_iff_of_sameCut hcut)

end GeneralizedEuler.Section2
