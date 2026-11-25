module

public import Section2.DiscCodes
public import Mathlib.Tactic.Linarith

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- Definition 3.23, written for maps on a specified domain. -/
def ConcentricOn (A : Set K) (f : K → K) : Prop :=
  ∀ c r, r ≠ 0 → openDisc O c r ⊆ A →
    ∃ c' r', r' ≠ 0 ∧ f '' openDisc O c r = openDisc O c' r'

def DiscToDiscOn (A B : Set K) (f g : K → K) : Prop :=
  Set.BijOn f A B ∧ Set.InvOn g f A B ∧ ConcentricOn O A f ∧ ConcentricOn O B g

/-- The proposed sufficient condition in the paragraph following 3.23. -/
def PreservesClosedDiscsOn (A : Set K) (f : K → K) : Prop :=
  ∀ c r, closedDisc O c r ⊆ A →
    ∃ c' r', f '' closedDisc O c r = closedDisc O c' r'

namespace GapExample

variable [LinearOrder K] [IsStrictOrderedRing K]

def domain : Set K := {x | x ≤ 0 ∨ 1 < x}

def closeGap (x : K) := if x ≤ 0 then x else x - 1

def openGap (x : K) := if x ≤ 0 then x else x + 1

theorem openGap_mem (x : K) : openGap x ∈ domain := by
  unfold openGap domain
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem close_open (x : K) : closeGap (openGap x) = x := by
  by_cases h : x ≤ 0
  · simp [openGap, closeGap, h]
  · simp [openGap, closeGap, h, show ¬ x + 1 ≤ 0 by linarith]

theorem open_close {x : K} (hx : x ∈ domain) : openGap (closeGap x) = x := by
  rcases hx with h | h
  · simp [openGap, closeGap, h]
  · simp [openGap, closeGap, show ¬ x ≤ 0 by linarith, show ¬ x - 1 ≤ 0 by linarith]

theorem bijOn : Set.BijOn (closeGap (K := K)) domain Set.univ :=
  ⟨fun _ _ => Set.mem_univ _, fun _ hx _ hy h =>
    (open_close hx).symm.trans ((congrArg openGap h).trans (open_close hy)),
   fun y _ => ⟨openGap y, openGap_mem y, close_open y⟩⟩

theorem preservesClosed (hO : IsOrderConvex O) :
    PreservesClosedDiscsOn O domain closeGap := by
  intro c r hsub
  have hc := valuativeDisc_ordConnected O hO c (Set.Iic r) (fun _ _ hab hb => hab.trans hb)
  by_cases hleft : ∀ x ∈ closedDisc O c r, x ≤ 0
  · refine ⟨c, r, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [closeGap, hleft y hy] using hy
    · intro hx
      exact ⟨x, hx, ite_eq_left (hleft x hx)⟩
  push Not at hleft
  obtain ⟨y, hy, hpos⟩ := hleft
  have hy' : 1 < y := (hsub hy).resolve_left hpos.not_ge
  have hright (x : K) (hx : x ∈ closedDisc O c r) : ¬ x ≤ 0 := by
    intro h
    have hone : (1 : K) ∈ closedDisc O c r := hc.out hx hy ⟨h.trans zero_le_one, hy'.le⟩
    exact (hsub hone).elim (by intro hbad; exact one_pos.not_ge hbad) (lt_irrefl _)
  refine ⟨c - 1, r, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change O.valuation (closeGap y - (c - 1)) ≤ r
    change O.valuation (y - c) ≤ r at hy
    simpa only [closeGap, ite_eq_right (hright y hy), sub_sub_sub_cancel_right] using hy
  · intro hx
    have h : x + 1 ∈ closedDisc O c r := by
      change O.valuation (x + 1 - c) ≤ r
      rwa [show x + 1 - c = x - (c - 1) by ring]
    exact ⟨x + 1, h, by simp [closeGap, hright _ h]⟩

/-- For every radius above one the inverse image under the bijection
of the open ball about zero contains 0 and 2 and misses 1. -/
theorem inverse_not_concentric (hO : IsOrderConvex O) {r : O.ValueGroup} (hr : 1 < r) :
    ¬ ConcentricOn O Set.univ openGap := by
  intro h
  obtain ⟨c, s, _, he⟩ := h 0 r (zero_lt_one.trans hr).ne' (Set.subset_univ _)
  have h₀ : (0 : K) ∈ openDisc O 0 r := mem_openDisc_center O (zero_lt_one.trans hr).ne' _
  have h₁ : (1 : K) ∈ openDisc O 0 r := by
    change O.valuation (1 - 0) < r
    simpa using hr
  have hleft : (0 : K) ∈ openDisc O c s := he ▸ ⟨0, h₀, by simp [openGap]⟩
  have hright : (1 + 1 : K) ∈ openDisc O c s := he ▸ ⟨1, h₁, by simp [openGap]⟩
  have hc := valuativeDisc_ordConnected O hO c (Set.Iio s) (fun _ _ hab hb => hab.trans_lt hb)
  have hone : (1 : K) ∈ openDisc O c s := hc.out hleft hright ⟨zero_le_one, by linarith⟩
  obtain ⟨z, _, hz⟩ := he.symm ▸ hone
  exact (hz ▸ openGap_mem z : (1 : K) ∈ domain).elim one_pos.not_ge (lt_irrefl _)

end GapExample
end GeneralizedEuler.Section3
