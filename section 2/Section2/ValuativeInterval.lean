module

public import Section2.ValuativeDisc

/-! Valuative intervals and their end discs in §2.4. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

/-- The end disc may be an open disc, a closed disc, or a singleton. -/
def IsEndDisc (D : Set K) : Prop :=
  (∃ c, D = {c}) ∨ ∃ c r, r ≠ 0 ∧ (D = openDisc O c r ∨ D = closedDisc O c r)

structure ValuativeIntervalEnd where
  disc : Set K
  included : Bool

def allowedBelow (e : Option (ValuativeIntervalEnd (K := K))) (x : K) : Prop :=
  match e with
  | none => True
  | some ⟨D, true⟩ => ∃ d ∈ D, x ≤ d
  | some ⟨D, false⟩ => ∀ d ∈ D, x < d

def allowedAbove (e : Option (ValuativeIntervalEnd (K := K))) (x : K) : Prop :=
  match e with
  | none => True
  | some ⟨D, true⟩ => ∃ d ∈ D, d ≤ x
  | some ⟨D, false⟩ => ∀ d ∈ D, d < x

/-- The set between two possibly unbounded end discs. Included endpoints
use the existential inequality in the manuscript. -/
def valuativeInterval (lo hi : Option (ValuativeIntervalEnd (K := K))) : Set K :=
  {x | allowedAbove lo x ∧ allowedBelow hi x}

def IsValuativeInterval (U : Set K) : Prop :=
  U.Nonempty ∧ ∃ lo hi : Option (ValuativeIntervalEnd (K := K)),
    (∀ e ∈ lo, IsEndDisc O e.disc) ∧ (∀ e ∈ hi, IsEndDisc O e.disc) ∧
    U = valuativeInterval lo hi

omit [Field K] [IsStrictOrderedRing K] in
private theorem allowedAbove_upward (e : Option (ValuativeIntervalEnd (K := K)))
    {x y : K} (hxy : x ≤ y) (h : allowedAbove e x) : allowedAbove e y := by
  rcases e with _ | ⟨D, b⟩
  · trivial
  cases b
  · exact fun z hz => (h z hz).trans_le hxy
  · obtain ⟨z, hz, hzx⟩ := h
    exact ⟨z, hz, hzx.trans hxy⟩

omit [Field K] [IsStrictOrderedRing K] in
private theorem allowedBelow_downward (e : Option (ValuativeIntervalEnd (K := K)))
    {x y : K} (hxy : x ≤ y) (h : allowedBelow e y) : allowedBelow e x := by
  rcases e with _ | ⟨D, b⟩
  · trivial
  cases b
  · exact fun z hz => hxy.trans_lt (h z hz)
  · obtain ⟨z, hz, hyz⟩ := h
    exact ⟨z, hz, hxy.trans hyz⟩

omit [Field K] [IsStrictOrderedRing K] in
theorem valuativeInterval_ordConnected (lo hi : Option (ValuativeIntervalEnd (K := K))) :
    Set.OrdConnected (valuativeInterval lo hi) := by
  refine ⟨?_⟩
  intro x hx y hy z ⟨hxz, hzy⟩
  exact ⟨allowedAbove_upward lo hxz hx.1, allowedBelow_downward hi hzy hy.2⟩

omit [Field K] [IsStrictOrderedRing K] in
theorem valuativeInterval_closed_singletons (a b : K) :
    valuativeInterval (some ⟨{a}, true⟩) (some ⟨{b}, true⟩) = Set.Icc a b := by
  ext x
  simp [valuativeInterval, allowedAbove, allowedBelow]

omit [Field K] [IsStrictOrderedRing K] in
theorem valuativeInterval_open_singletons (a b : K) :
    valuativeInterval (some ⟨{a}, false⟩) (some ⟨{b}, false⟩) = Set.Ioo a b := by
  ext x
  simp [valuativeInterval, allowedAbove, allowedBelow]

/-- The component sets in a Holly normal form. Different descriptions of
the same interval by ends give the same component. -/
def IsHollyDecomposition (U : Set K) (pieces : Finset (Set K)) : Prop :=
  (∀ D ∈ pieces, IsValuativeInterval O D) ∧ U = ⋃ D ∈ pieces, D ∧
    ∀ D ∈ pieces, ∀ B ∈ pieces, D ≠ B → ¬ IsValuativeInterval O (D ∪ B)

end GeneralizedEuler.Section2
