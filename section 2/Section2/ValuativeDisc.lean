module

public import Section2.ResidueOrder

/-! Valuative discs and the quotient of a closed disc by its open children.
The radius is in Mathlib's multiplicative order, dual to additive values. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

def openDisc (c : K) (r : O.ValueGroup) : Set K := {x | O.valuation (x - c) < r}

def closedDisc (c : K) (r : O.ValueGroup) : Set K := {x | O.valuation (x - c) ≤ r}

theorem mem_openDisc_center {r : O.ValueGroup} (hr : r ≠ 0) (c : K) :
    c ∈ openDisc O c r := by
  change O.valuation (c - c) < r
  rw [sub_self, map_zero]
  exact pos_iff_ne_zero.mpr hr

theorem mem_closedDisc_center (r : O.ValueGroup) (c : K) :
    c ∈ closedDisc O c r := by
  change O.valuation (c - c) ≤ r
  rw [sub_self, map_zero]
  exact zero_le

theorem openDisc_change_center {b c : K} {r : O.ValueGroup} (hb : b ∈ openDisc O c r) :
    openDisc O b r = openDisc O c r := by
  change O.valuation (b - c) < r at hb
  ext x
  change O.valuation (x - b) < r ↔ O.valuation (x - c) < r
  constructor
  · intro hx
    rw [← sub_add_sub_cancel x b c]
    exact (O.valuation.map_add _ _).trans_lt (max_lt hx hb)
  · intro hx
    rw [← sub_sub_sub_cancel_right x b c]
    exact (O.valuation.map_sub _ _).trans_lt (max_lt hx hb)

theorem closedDisc_change_center {b c : K} {r : O.ValueGroup}
    (hb : b ∈ closedDisc O c r) : closedDisc O b r = closedDisc O c r := by
  change O.valuation (b - c) ≤ r at hb
  ext x
  change O.valuation (x - b) ≤ r ↔ O.valuation (x - c) ≤ r
  constructor
  · intro hx
    rw [← sub_add_sub_cancel x b c]
    exact (O.valuation.map_add _ _).trans (max_le hx hb)
  · intro hx
    rw [← sub_sub_sub_cancel_right x b c]
    exact (O.valuation.map_sub _ _).trans (max_le hx hb)

theorem openDisc_subset_closedDisc {c : K} {r : O.ValueGroup} :
    openDisc O c r ⊆ closedDisc O c r := by
  intro x hx
  change O.valuation (x - c) ≤ r
  exact le_of_lt (show O.valuation (x - c) < r from hx)

theorem openDisc_ssubset_closedDisc {c : K} {r : O.ValueGroup} :
    openDisc O c r ⊂ closedDisc O c r := by
  obtain ⟨d, hd⟩ := O.valuation_surjective r
  refine ⟨openDisc_subset_closedDisc O, ?_⟩
  intro h
  have hvalue : O.valuation (c + d - c) = r := by
    rw [add_sub_cancel_left, hd]
  have hc : c + d ∈ closedDisc O c r := hvalue.le
  exact (ne_of_lt (h hc)) hvalue

/-- The open disc of the parent's radius through a point is the largest
proper open subdisc of the parent through that point. -/
theorem openDisc_maximal_proper {c y b : K} {r s : O.ValueGroup}
    (hy : y ∈ openDisc O b s) (h : openDisc O b s ⊂ closedDisc O c r) :
    openDisc O b s ⊆ openDisc O y r := by
  have hyc := h.1 hy
  rw [← openDisc_change_center O hy] at h ⊢
  have hrs : s ≤ r := by
    by_contra! hlt
    apply h.2
    rw [← closedDisc_change_center O hyc]
    intro x hx
    exact lt_of_le_of_lt hx hlt
  intro x hx
  exact lt_of_lt_of_le hx hrs

theorem openChild_maximal_proper {c y : K} {r : O.ValueGroup}
    (hr : r ≠ 0) (hy : y ∈ closedDisc O c r) :
    y ∈ openDisc O y r ∧ openDisc O y r ⊂ closedDisc O c r := by
  refine ⟨mem_openDisc_center O hr y, ?_⟩
  rw [← closedDisc_change_center O hy]
  exact openDisc_ssubset_closedDisc O

theorem rv_fiber_eq_openDisc {c : K} (hc : c ≠ 0) :
    rv O ⁻¹' {rv O c} = openDisc O c (O.valuation c) := by
  ext x
  exact rv_eq_rv_iff_valuation O hc

/-- The equivalence relation on a closed disc whose classes are its open
children. It applies to the center as well as to the outer shell. -/
def openChildSetoid (c : K) (r : O.ValueGroup) (hr : r ≠ 0) :
    Setoid (closedDisc O c r) where
  r x y := O.valuation ((x : K) - y) < r
  iseqv :=
    ⟨fun x => mem_openDisc_center O hr x,
     fun {x y} h => by
        change O.valuation ((x : K) - y) < r at h
        rwa [← neg_sub, O.valuation.map_neg],
     fun {x y z} hxy hyz => by
        rw [← sub_add_sub_cancel (x : K) (y : K) (z : K)]
        exact (O.valuation.map_add _ _).trans_lt (max_lt hxy hyz)⟩

abbrev DiscChildren (c : K) (r : O.ValueGroup) (hr : r ≠ 0) :=
  Quotient (openChildSetoid O c r hr)

theorem openChildSetoid_fiber (c : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (x y : closedDisc O c r) :
    (⟦x⟧ : DiscChildren O c r hr) = ⟦y⟧ ↔ (x : K) ∈ openDisc O (y : K) r :=
  Quotient.eq

private theorem normalization_mem {c d : K} {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : O.valuation d = r) (x : closedDisc O c r) :
    ((x : K) - c) / d ∈ O := by
  rw [← O.valuation_le_one_iff, map_div₀, hd, div_le_one₀ (pos_iff_ne_zero.mpr hr)]
  exact x.property

private def normalizedPoint (c d : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : O.valuation d = r) (x : closedDisc O c r) : O :=
  ⟨((x : K) - c) / d, normalization_mem O hr hd x⟩

private theorem normalizedPoint_surjective (c d : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : O.valuation d = r) : Function.Surjective (normalizedPoint O c d hr hd) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hr (hd.symm.trans (map_zero O.valuation))
  intro y
  have hy : c + (y : K) * d ∈ closedDisc O c r := by
    change O.valuation (c + (y : K) * d - c) ≤ r
    rw [add_sub_cancel_left, map_mul O.valuation, hd]
    exact mul_le_of_le_one_left (zero_le : 0 ≤ r) (O.valuation_le_one y)
  refine ⟨⟨c + (y : K) * d, hy⟩, Subtype.ext ?_⟩
  change (c + (y : K) * d - c) / d = y
  rw [add_sub_cancel_left, mul_div_cancel_right₀ (y : K) hd0]

private theorem normalizedResidue_eq_iff (c d : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : O.valuation d = r) (x y : closedDisc O c r) :
    IsLocalRing.residue O (normalizedPoint O c d hr hd x) =
      IsLocalRing.residue O (normalizedPoint O c d hr hd y) ↔
      O.valuation ((x : K) - y) < r := by
  rw [residue_eq_iff_valuation_sub_lt_one]
  change O.valuation ((((x : K) - c) / d) - (((y : K) - c) / d)) < 1 ↔ _
  rw [← sub_div, sub_sub_sub_cancel_right, map_div₀, hd, div_lt_one₀ (pos_iff_ne_zero.mpr hr)]

/-- A closed disc's affine residue chart. Its central child is the whole
open disc about the center, represented by zero in the residue field. -/
def discChildrenChart (c d : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : O.valuation d = r) : DiscChildren O c r hr ≃ Residue O := by
  let F : DiscChildren O c r hr → Residue O :=
    Quotient.lift (IsLocalRing.residue O ∘ normalizedPoint O c d hr hd)
      (fun x y h => (normalizedResidue_eq_iff O c d hr hd x y).mpr h)
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y => exact Quotient.sound ((normalizedResidue_eq_iff O c d hr hd x y).mp hxy)
  · intro s
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective s
    obtain ⟨x, rfl⟩ := normalizedPoint_surjective O c d hr hd y
    exact ⟨⟦x⟧, rfl⟩

theorem discChildrenChart_eq_zero_iff (c d : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : O.valuation d = r) (x : closedDisc O c r) :
    discChildrenChart O c d hr hd ⟦x⟧ = 0 ↔ (x : K) ∈ openDisc O c r := by
  let y : closedDisc O c r := ⟨c, mem_closedDisc_center O r c⟩
  have hy : normalizedPoint O c d hr hd y = 0 := by
    apply Subtype.ext
    change (c - c) / d = 0
    rw [sub_self, zero_div]
  have h := normalizedResidue_eq_iff O c d hr hd x y
  rw [hy, map_zero] at h
  exact h

end GeneralizedEuler.Section2
