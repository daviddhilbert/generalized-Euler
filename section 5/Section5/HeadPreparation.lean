module

public import Section5.FiniteCenters

/-! A family of finite-center preparations. Pairwise leading terms of
the centers determine the available labels and the locus of each step. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] {O : ValuationSubring K}

namespace UnaryPreparation

variable {H : Type*} (P : UnaryPreparation O H)

/-- Appending a center changes the allowed new leading terms only on the
nonzero fiber containing that center. This describes the full history. -/
theorem step_label_range (c : K) (t : H) (u : RV0 O) :
    (t, u) ∈ Set.range (P.step c).label ↔
      t ∈ Set.range P.label ∧
        ((P.lead t ≠ 0 ∧ rv O (c - P.offset t) = P.lead t) →
          unsignedValue O u < unsignedValue O (P.lead t)) ∧
        (¬ (P.lead t ≠ 0 ∧ rv O (c - P.offset t) = P.lead t) → u = P.lead t) := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨ht, hu⟩ := Prod.mk.inj hx
    change P.label x = t at ht
    change rv O (x - P.nextOffset c (P.label x)) = u at hu
    have hlead := P.leading x
    rw [ht] at hu hlead
    refine ⟨⟨x, ht⟩, ?_, ?_⟩
    · intro h
      have hn : c - P.offset t ≠ 0 :=
        (rv_eq_zero_iff O).not.mp (h.2.symm ▸ h.1)
      have hv := (rv_eq_rv_iff_valuation O hn).mp (hlead.trans h.2.symm)
      rw [sub_sub_sub_cancel_right] at hv
      have hu' : rv O (x - c) = u := by simpa [nextOffset, h] using hu
      rwa [← hu', unsignedValue_rv, ← h.2, unsignedValue_rv]
    · intro h
      exact (by simpa [nextOffset, h] using hu.symm : u = rv O (x - P.offset t)).trans hlead
  · rintro ⟨⟨x, hx⟩, hmove, hstay⟩
    by_cases h : P.lead t ≠ 0 ∧ rv O (c - P.offset t) = P.lead t
    · obtain ⟨y, hy⟩ := rv_surjective O u
      have hv := hmove h
      rw [← hy, unsignedValue_rv, ← h.2, unsignedValue_rv] at hv
      have hn : c - P.offset t ≠ 0 :=
        (rv_eq_zero_iff O).not.mp (h.2.symm ▸ h.1)
      let z := y + c
      have hz : P.label z = t := by
        have hrv : rv O (z - P.offset t) = P.lead t := by
          rw [← h.2, rv_eq_rv_iff_valuation O hn, sub_sub_sub_cancel_right]
          simpa [z] using hv
        apply Eq.trans (P.constant_label (by rwa [hx])) hx
      refine ⟨z, Prod.ext hz ?_⟩
      change rv O (z - P.nextOffset c (P.label z)) = u
      rw [hz]
      simpa [nextOffset, h, z] using hy
    · refine ⟨x, Prod.ext hx ?_⟩
      change rv O (x - P.nextOffset c (P.label x)) = u
      rw [hx]
      have hlead := P.leading x
      rw [hx] at hlead
      simpa [nextOffset, h, hstay h] using hlead

end UnaryPreparation

section IndexedCenters

open UnaryPreparation

variable {I : Type*} (center : Option I → K)

abbrev centerPreparation (center : Option I → K) (cs : List I) :=
  (regularize (O := O)).prepare (center ∘ some) cs

/-- Record which center furnished the cumulative offset at each label.
The initial index `none` represents zero. -/
private def offsetIndex (O : ValuationSubring K) (center : Option I → K) :
    (cs : List I) → PreparationLabels O (RV0 O) cs.length → Option I
  | [], _ => none
  | c :: cs, t => by
    classical
    let old := offsetIndex O center cs t.1
    exact if (centerPreparation (O := O) center cs).lead t.1 ≠ 0 ∧
      rv O (center (some c) - center old) = (centerPreparation (O := O) center cs).lead t.1
      then some c else old

private theorem offset_eq_center (hzero : center none = 0) (cs : List I) :
    ∀ t, (centerPreparation (O := O) center cs).offset t = center (offsetIndex O center cs t) := by
  classical
  induction cs with
  | nil => exact fun _ => hzero.symm
  | cons c cs ih =>
    intro t
    change (centerPreparation (O := O) center cs).nextOffset (center (some c)) t.1 =
      center (offsetIndex O center (c :: cs) t)
    simp only [nextOffset, offsetIndex, ih]
    split <;> rfl

theorem centerPreparation_lead_independent (other : Option I → K) (cs : List I) :
    (centerPreparation (O := O) center cs).lead = (centerPreparation (O := O) other cs).lead := by
  cases cs <;> rfl

private theorem offsetIndex_eq (other : Option I → K)
    (h : ∀ i j, rv O (center i - center j) = rv O (other i - other j)) (cs : List I) :
    ∀ t, offsetIndex O center cs t = offsetIndex O other cs t := by
  classical
  induction cs with
  | nil => intro t; rfl
  | cons c cs ih =>
    intro t
    simp only [offsetIndex, ih, h, centerPreparation_lead_independent (O := O) center other cs]

/-- A center is usable in precisely the same old histories whenever
the ordered differences of centers agree. -/
theorem centerStep_same_locus (other : Option I → K)
    (hzero : center none = 0) (hzero' : other none = 0)
    (h : ∀ i j, rv O (center i - center j) = rv O (other i - other j)) (cs : List I)
    (i : I) (t : PreparationLabels O (RV0 O) cs.length) :
    ((centerPreparation (O := O) center cs).lead t ≠ 0 ∧
      rv O (center (some i) - (centerPreparation (O := O) center cs).offset t) =
        (centerPreparation (O := O) center cs).lead t) ↔
    ((centerPreparation (O := O) other cs).lead t ≠ 0 ∧
      rv O (other (some i) - (centerPreparation (O := O) other cs).offset t) =
        (centerPreparation (O := O) other cs).lead t) := by
  rw [offset_eq_center (O := O) center hzero, offset_eq_center (O := O) other hzero',
    offsetIndex_eq (O := O) center other h, h, centerPreparation_lead_independent (O := O) center other cs]

/-- Equality of the leading terms of all ordered differences, including
the differences with zero, gives the same output histories in the two
fibers. Hence the locus and the available RV labels descend together. -/
theorem label_ranges_of_center_differences (other : Option I → K)
    (hzero : center none = 0) (hzero' : other none = 0)
    (h : ∀ i j, rv O (center i - center j) = rv O (other i - other j)) (cs : List I) :
    Set.range (centerPreparation (O := O) center cs).label =
      Set.range (centerPreparation (O := O) other cs).label := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    ext t
    rcases t with ⟨s, u⟩
    change (s,u) ∈ Set.range ((centerPreparation (O := O) center cs).step (center (some c))).label ↔
      (s,u) ∈ Set.range ((centerPreparation (O := O) other cs).step (other (some c))).label
    rw [step_label_range, step_label_range, ih,
      offset_eq_center (O := O) center hzero, offset_eq_center (O := O) other hzero',
      offsetIndex_eq (O := O) center other h, h, centerPreparation_lead_independent (O := O) center other cs]

end IndexedCenters

end GeneralizedEuler.Section5
