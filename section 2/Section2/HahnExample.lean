module

public import Section2.LeadingTerm
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.HahnSeries.Lex
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Section2.CanonicalModel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The Hahn-field and leading-term calculation in Example 2.8. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open HahnSeries

abbrev RealRationalHahn := HahnSeries ℚ ℝ

/-- The Hahn valuation, in the multiplicative order used by Mathlib. -/
def realRationalHahnValuation : Valuation RealRationalHahn (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  AddValuation.toValuation (HahnSeries.addVal ℚ ℝ)

abbrev realRationalHahnRing : ValuationSubring RealRationalHahn :=
  realRationalHahnValuation.valuationSubring

/-- Nonnegative leading exponent is precisely integrality. -/
theorem mem_realRationalHahnRing_iff (x : RealRationalHahn) :
    x ∈ realRationalHahnRing ↔ 0 ≤ x.orderTop := by
  change realRationalHahnValuation x ≤ 1 ↔ 0 ≤ x.orderTop
  rw [realRationalHahnValuation, AddValuation.toValuation_apply, HahnSeries.addVal_apply]
  rfl

theorem realRationalHahn_valuation_lt_iff (x y : RealRationalHahn) :
    realRationalHahnRing.valuation x < realRationalHahnRing.valuation y ↔
      y.orderTop < x.orderTop := by
  have h := Valuation.isEquiv_valuation_valuationSubring realRationalHahnValuation
  exact (h.lt_iff_lt (x := x) (y := y)).symm.trans (by
    rw [realRationalHahnValuation, AddValuation.toValuation_apply, AddValuation.toValuation_apply,
      HahnSeries.addVal_apply, HahnSeries.addVal_apply]
    rfl)

private theorem hahn_orderTop_eq_of_diff_gt {x y : RealRationalHahn}
    (h : y.orderTop < (x - y).orderTop) : x.orderTop = y.orderTop := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hx
    have hsub := HahnSeries.orderTop_sub hx
    have hd : (x - y).orderTop = (y - x).orderTop := by
      rw [← neg_sub, HahnSeries.orderTop_neg]
    rw [hd, hsub] at h
    exact (lt_irrefl _) h
  · apply le_of_not_gt
    intro hx
    rw [HahnSeries.orderTop_sub hx] at h
    exact (lt_asymm hx) h

/-- Two Hahn series have the same RV class exactly when both leading
exponent and leading coefficient agree. This includes the zero class. -/
theorem hahn_rv_eq_iff_leading_pair (x y : RealRationalHahn) :
    rv realRationalHahnRing x = rv realRationalHahnRing y ↔
      x.orderTop = y.orderTop ∧ x.leadingCoeff = y.leadingCoeff := by
  by_cases hy : y = 0
  · subst y
    rw [map_zero, rv_eq_zero_iff, HahnSeries.orderTop_zero, HahnSeries.leadingCoeff_zero,
      HahnSeries.leadingCoeff_eq_zero]
    exact ⟨fun h => ⟨h ▸ HahnSeries.orderTop_zero, h⟩, And.right⟩
  · rw [rv_eq_rv_iff_valuation realRationalHahnRing hy, realRationalHahn_valuation_lt_iff]
    constructor
    · intro h
      have ho := hahn_orderTop_eq_of_diff_gt h
      have hx : x ≠ 0 := by
        intro h0
        rw [h0, HahnSeries.orderTop_zero] at ho
        exact hy (HahnSeries.orderTop_eq_top.mp ho.symm)
      have hq : x.order = y.order := WithTop.coe_eq_coe.mp
        ((HahnSeries.order_eq_orderTop_of_ne_zero hx).trans
          (ho.trans (HahnSeries.order_eq_orderTop_of_ne_zero hy).symm))
      have hlt : (y.order : WithTop ℚ) < (x - y).orderTop :=
        (HahnSeries.order_eq_orderTop_of_ne_zero hy) ▸ h
      have hz := HahnSeries.coeff_eq_zero_of_lt_orderTop hlt
      rw [HahnSeries.coeff_sub, sub_eq_zero] at hz
      exact ⟨ho, by rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hq, hz]⟩
    · rintro ⟨ho, hc⟩
      have hq := (HahnSeries.order_eq_orderTop_of_ne_zero hy).symm
      rw [hq]
      exact HahnSeries.le_orderTop_of_leadingCoeff_eq (ho.trans hq) hq hc

/-- Each nonzero RV class has its leading monomial as a representative. -/
theorem hahn_rv_eq_single_leading (x : RealRationalHahn) (hx : x ≠ 0) :
    rv realRationalHahnRing x =
      rv realRationalHahnRing (HahnSeries.single x.order x.leadingCoeff) := by
  apply (hahn_rv_eq_iff_leading_pair _ _).mpr
  refine ⟨?_, (HahnSeries.leadingCoeff_of_single).symm⟩
  rw [HahnSeries.orderTop_single (HahnSeries.leadingCoeff_ne_zero.mpr hx),
    HahnSeries.order_eq_orderTop_of_ne_zero hx]

/-- Nonzero Hahn leading coordinates are an exponent and a nonzero
coefficient. The extra element is the RV zero. -/
abbrev HahnLeadingCoordinates := WithZero (Multiplicative ℚ × ℝˣ)

def hahnLeadingCoordinates : RealRationalHahn →*₀ HahnLeadingCoordinates := by
  classical
  exact {
    toFun := fun x => if h : x = 0 then 0 else
      ((Multiplicative.ofAdd x.order, Units.mk0 x.leadingCoeff (HahnSeries.leadingCoeff_ne_zero.mpr h)) :
        Multiplicative ℚ × ℝˣ)
    map_zero' := by simp
    map_one' := by
      simp only [one_ne_zero, dite_false, HahnSeries.order_one, HahnSeries.leadingCoeff_one,
        ← WithZero.coe_one, WithZero.coe_inj]
      exact Prod.ext rfl (Units.ext rfl)
    map_mul' := fun x y => by
      by_cases hx : x = 0
      · subst x
        simp
      by_cases hy : y = 0
      · subst y
        simp
      simp only [hx, hy, mul_ne_zero hx hy, dite_false, ← WithZero.coe_mul, WithZero.coe_inj]
      apply Prod.ext
      · exact congrArg Multiplicative.ofAdd (HahnSeries.order_mul hx hy)
      · apply Units.ext
        exact HahnSeries.leadingCoeff_mul x y }

theorem hahnLeadingCoordinates_apply_ne_zero {x : RealRationalHahn} (hx : x ≠ 0) :
    hahnLeadingCoordinates x =
      ((Multiplicative.ofAdd x.order, Units.mk0 x.leadingCoeff (HahnSeries.leadingCoeff_ne_zero.mpr hx)) :
        Multiplicative ℚ × ℝˣ) := by
  classical
  change (if h : x = 0 then 0 else _) = _
  rw [dite_eq_right hx]

theorem hahnLeadingCoordinates_single (q : ℚ) (c : ℝˣ) :
    hahnLeadingCoordinates (HahnSeries.single q (c : ℝ)) = ((Multiplicative.ofAdd q, c) :
        Multiplicative ℚ × ℝˣ) := by
  have hc : (c : ℝ) ≠ 0 := c.ne_zero
  have hs : (HahnSeries.single q (c : ℝ)) ≠ 0 := by
    exact HahnSeries.leadingCoeff_ne_zero.mp (by rwa [HahnSeries.leadingCoeff_of_single])
  rw [hahnLeadingCoordinates_apply_ne_zero hs, WithZero.coe_inj]
  apply Prod.ext
  · exact congrArg Multiplicative.ofAdd (HahnSeries.order_single hc)
  · exact Units.ext (HahnSeries.leadingCoeff_of_single)

theorem hahnLeadingCoordinates_surjective : Function.Surjective hahnLeadingCoordinates := by
  intro z
  refine WithZero.recZeroCoe ⟨0, map_zero hahnLeadingCoordinates⟩ (fun p => ?_) z
  exact ⟨HahnSeries.single p.1.toAdd (p.2 : ℝ), hahnLeadingCoordinates_single _ _⟩

theorem hahnLeadingCoordinates_eq_iff_rv_eq (x y : RealRationalHahn) :
    hahnLeadingCoordinates x = hahnLeadingCoordinates y ↔
      rv realRationalHahnRing x = rv realRationalHahnRing y := by
  by_cases hx : x = 0
  · subst x
    rw [map_zero, map_zero, eq_comm (a := (0 : HahnLeadingCoordinates)), eq_comm (a := (0 : RV0 realRationalHahnRing)),
      map_eq_zero, rv_eq_zero_iff]
  by_cases hy : y = 0
  · subst y
    rw [map_zero, map_zero, map_eq_zero, rv_eq_zero_iff]
  rw [hahnLeadingCoordinates_apply_ne_zero hx, hahnLeadingCoordinates_apply_ne_zero hy, WithZero.coe_inj,
    hahn_rv_eq_iff_leading_pair, ← HahnSeries.order_eq_orderTop_of_ne_zero hx, ← HahnSeries.order_eq_orderTop_of_ne_zero hy,
    WithTop.coe_eq_coe]
  constructor
  · intro h
    exact ⟨congrArg (fun p : Multiplicative ℚ × ℝˣ => p.1.toAdd) h,
      congrArg (fun p : Multiplicative ℚ × ℝˣ => (p.2 : ℝ)) h⟩
  · rintro ⟨hq, hc⟩
    exact Prod.ext (congrArg Multiplicative.ofAdd hq) (Units.ext hc)

private def rvEquivFromCoordinates {K C : Type*} [Field K] [MonoidWithZero C]
    (O : ValuationSubring K) (f : K →*₀ C) (hSurj : Function.Surjective f)
    (hClasses : ∀ x y, f x = f y ↔ rv O x = rv O y) :
    RV0 O ≃* C := by
  let encode (t : RV0 O) := f ((rv_surjective O t).choose)
  have hEncode (x : K) : encode (rv O x) = f x :=
    (hClasses _ _).mpr ((rv_surjective O (rv O x)).choose_spec)
  have hInjective : Function.Injective encode := by
    intro x y h
    obtain ⟨a, rfl⟩ := rv_surjective O x
    obtain ⟨b, rfl⟩ := rv_surjective O y
    exact (hClasses a b).mp ((hEncode a).symm.trans (h.trans (hEncode b)))
  have hSurjective : Function.Surjective encode := by
    intro t
    obtain ⟨a, rfl⟩ := hSurj t
    exact ⟨rv O a, hEncode a⟩
  refine { Equiv.ofBijective encode ⟨hInjective, hSurjective⟩ with map_mul' := ?_ }
  intro x y
  obtain ⟨a, rfl⟩ := rv_surjective O x
  obtain ⟨b, rfl⟩ := rv_surjective O y
  change encode (rv O a * rv O b) = encode (rv O a) * encode (rv O b)
  rw [← map_mul, hEncode, hEncode, hEncode, map_mul]

/-- The leading-term quotient in Example 2.8 has the stated
multiplicative coordinates. -/
def hahnRVEquiv := rvEquivFromCoordinates realRationalHahnRing hahnLeadingCoordinates
  hahnLeadingCoordinates_surjective hahnLeadingCoordinates_eq_iff_rv_eq

@[simp] theorem hahnRVEquiv_rv (x : RealRationalHahn) :
    hahnRVEquiv (rv realRationalHahnRing x) = hahnLeadingCoordinates x :=
  (hahnLeadingCoordinates_eq_iff_rv_eq _ _).mpr ((rv_surjective _ _).choose_spec)

private theorem hahn_rv_single_eq_iff {q r : ℚ} {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    rv realRationalHahnRing (HahnSeries.single q c) =
      rv realRationalHahnRing (HahnSeries.single r d) ↔ q = r ∧ c = d := by
  rw [hahn_rv_eq_iff_leading_pair, HahnSeries.orderTop_single hc, HahnSeries.orderTop_single hd,
    WithTop.coe_eq_coe, HahnSeries.leadingCoeff_of_single, HahnSeries.leadingCoeff_of_single]

private def hahnCoefficientSign (c : ℝ) : ℝ := if c < 0 then -1 else 1

private theorem hahnCoefficientSign_mul {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    hahnCoefficientSign (c * d) = hahnCoefficientSign c * hahnCoefficientSign d := by
  rcases lt_or_gt_of_ne hc with hc | hc <;> rcases lt_or_gt_of_ne hd with hd | hd
  · simp [hahnCoefficientSign, hc, hd, (mul_pos_of_neg_of_neg hc hd).not_gt]
  · simp [hahnCoefficientSign, hc, hd.not_gt, mul_neg_of_neg_of_pos hc hd]
  · simp [hahnCoefficientSign, hc.not_gt, hd, mul_neg_of_pos_of_neg hc hd]
  · simp [hahnCoefficientSign, hc.not_gt, hd.not_gt, (mul_pos hc hd).not_gt]

def hahnSignedCoordinateHom : (Multiplicative ℚ × ℝˣ) →* ℝ where
  toFun p := hahnCoefficientSign (p.2 : ℝ) * Real.exp (-(p.1.toAdd : ℝ))
  map_one' := by change hahnCoefficientSign 1 * Real.exp (-(↑(0 : ℚ) : ℝ)) = 1; simp [hahnCoefficientSign]
  map_mul' p q := by
    change hahnCoefficientSign ((p.2 : ℝ) * ↑q.2) * Real.exp (-((p.1.toAdd + q.1.toAdd : ℚ) : ℝ)) =
      hahnCoefficientSign (p.2 : ℝ) * Real.exp (-(p.1.toAdd : ℝ)) *
        (hahnCoefficientSign (q.2 : ℝ) * Real.exp (-(q.1.toAdd : ℝ)))
    rw [hahnCoefficientSign_mul p.2.ne_zero q.2.ne_zero, Rat.cast_add, neg_add, Real.exp_add]
    ac_rfl

/-- The signed valuation in Example 2.8, including its value at zero. -/
def hahnSignedValue : RealRationalHahn →*₀ ℝ :=
  (WithZero.lift' hahnSignedCoordinateHom).comp hahnLeadingCoordinates

theorem hahnSignedValue_apply_ne_zero {x : RealRationalHahn} (hx : x ≠ 0) :
    hahnSignedValue x =
      (if x.leadingCoeff < 0 then -1 else 1) * Real.exp (-(x.order : ℝ)) := by
  change WithZero.lift' hahnSignedCoordinateHom (hahnLeadingCoordinates x) = _
  rw [hahnLeadingCoordinates_apply_ne_zero hx]
  rfl

/-- The signed valuation factors through the leading-term class. -/
theorem hahnSignedValue_eq_of_rv_eq {x y : RealRationalHahn}
    (h : rv realRationalHahnRing x = rv realRationalHahnRing y) :
    hahnSignedValue x = hahnSignedValue y :=
  congrArg (WithZero.lift' hahnSignedCoordinateHom) ((hahnLeadingCoordinates_eq_iff_rv_eq x y).mpr h)

/-- On nonzero classes the signed valuation has kernel the positive
real coefficient group at exponent zero. -/
theorem hahnSignedCoordinateHom_eq_one_iff (q : ℚ) (c : ℝˣ) :
    hahnSignedCoordinateHom (Multiplicative.ofAdd q, c) = 1 ↔ q = 0 ∧ 0 < (c : ℝ) := by
  change hahnCoefficientSign (c : ℝ) * Real.exp (-(q : ℝ)) = 1 ↔ q = 0 ∧ 0 < (c : ℝ)
  rcases lt_or_gt_of_ne c.ne_zero with h | h
  · simp only [hahnCoefficientSign, h, ↓reduceIte, neg_one_mul]
    refine ⟨fun he => ?_, fun he => (h.not_gt he.2).elim⟩
    have hn := neg_neg_of_pos (Real.exp_pos (-(q : ℝ)))
    rw [he] at hn
    exact (not_lt_of_ge zero_le_one hn).elim
  · simp [hahnCoefficientSign, h, h.not_gt, Real.exp_eq_one_iff]

/-- The nonzero signed values are exactly the reals of the form
(e^{-q}) and (-e^{-q}) for rational (q). -/
theorem hahnSignedCoordinateHom_range :
    Set.range hahnSignedCoordinateHom =
      {y | ∃ q : ℚ, y = Real.exp (-(q : ℝ)) ∨ y = -Real.exp (-(q : ℝ))} := by
  ext y
  constructor
  · rintro ⟨⟨q, c⟩, rfl⟩
    refine ⟨q.toAdd, ?_⟩
    change hahnCoefficientSign (c : ℝ) * Real.exp (-(q.toAdd : ℝ)) = _ ∨
      hahnCoefficientSign (c : ℝ) * Real.exp (-(q.toAdd : ℝ)) = _
    by_cases h : (c : ℝ) < 0 <;> simp [hahnCoefficientSign, h]
  · rintro ⟨q, rfl | rfl⟩
    · refine ⟨(Multiplicative.ofAdd q, (1 : ℝˣ)), ?_⟩
      change hahnCoefficientSign (1 : ℝ) * Real.exp (-(q : ℝ)) = _
      simp [hahnCoefficientSign]
    · refine ⟨(Multiplicative.ofAdd q, (-1 : ℝˣ)), ?_⟩
      change hahnCoefficientSign (-1 : ℝ) * Real.exp (-(q : ℝ)) = _
      simp [hahnCoefficientSign]

private theorem order_eq_zero_of_orderTop_eq_zero {x : RealRationalHahn}
    (h : x.orderTop = 0) : x.order = 0 := by
  have hn : x ≠ 0 := by
    intro hz
    rw [hz, HahnSeries.orderTop_zero] at h
    exact WithTop.top_ne_coe h
  have he := (HahnSeries.order_eq_orderTop_of_ne_zero hn).trans h
  exact WithTop.coe_eq_coe.mp he

private theorem hahn_coeff_mul_at_zero (a b : realRationalHahnRing) :
    ((a.val * b.val) : RealRationalHahn).coeff 0 = a.val.coeff 0 * b.val.coeff 0 := by
  have ha := (mem_realRationalHahnRing_iff a.val).mp a.property
  have hb := (mem_realRationalHahnRing_iff b.val).mp b.property
  rcases ha.eq_or_lt with ha | ha
  · rcases hb.eq_or_lt with hb | hb
    · have ha0 := order_eq_zero_of_orderTop_eq_zero ha.symm
      have hb0 := order_eq_zero_of_orderTop_eq_zero hb.symm
      have h := HahnSeries.coeff_mul_order_add_order a.val b.val
      rwa [ha0, hb0, add_zero, HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, ha0, hb0] at h
    · have hp : (0 : WithTop ℚ) < (a.val * b.val).orderTop := by
        rw [HahnSeries.orderTop_mul, ← ha, zero_add]
        exact hb
      rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hp, HahnSeries.coeff_eq_zero_of_lt_orderTop hb, mul_zero]
  · have hp : (0 : WithTop ℚ) < (a.val * b.val).orderTop := by
      rw [HahnSeries.orderTop_mul]
      exact ha.trans_le (le_add_of_nonneg_right hb)
    rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hp, HahnSeries.coeff_eq_zero_of_lt_orderTop ha, zero_mul]

/-- The residue of an integral Hahn series is its constant coefficient. -/
def hahnConstantCoefficient : realRationalHahnRing →+* ℝ where
  toFun x := x.val.coeff 0
  map_zero' := by change (0 : RealRationalHahn).coeff 0 = 0; simp
  map_one' := by change (1 : RealRationalHahn).coeff 0 = 1; simp
  map_add' _ _ := HahnSeries.coeff_add
  map_mul' := hahn_coeff_mul_at_zero

theorem hahnConstantCoefficient_surjective : Function.Surjective hahnConstantCoefficient := by
  intro c
  have h : HahnSeries.single (0 : ℚ) c ∈ realRationalHahnRing := by
    rw [mem_realRationalHahnRing_iff]
    exact HahnSeries.orderTop_single_le (a := (0 : ℚ))
  refine ⟨⟨_, h⟩, ?_⟩
  exact HahnSeries.coeff_single_same 0 c

theorem hahnConstantCoefficient_ker :
    RingHom.ker hahnConstantCoefficient = IsLocalRing.maximalIdeal realRationalHahnRing := by
  ext x
  rw [RingHom.mem_ker]
  change x.val.coeff 0 = 0 ↔ x ∈ IsLocalRing.maximalIdeal realRationalHahnValuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff]
  change x.val.coeff 0 = 0 ↔ realRationalHahnValuation x.val < 1
  rw [realRationalHahnValuation, AddValuation.toValuation_apply, HahnSeries.addVal_apply]
  change x.val.coeff 0 = 0 ↔ 0 < x.val.orderTop
  have h := (mem_realRationalHahnRing_iff x.val).mp x.property
  constructor
  · intro hx
    apply h.lt_of_ne
    intro he
    have hne : x.val ≠ 0 := by
      intro hz
      rw [hz, HahnSeries.orderTop_zero] at he
      exact WithTop.top_ne_coe he.symm
    have ho := order_eq_zero_of_orderTop_eq_zero he.symm
    have hc := HahnSeries.leadingCoeff_ne_zero.mpr hne
    rw [HahnSeries.leadingCoeff_eq, ho, hx] at hc
    exact hc rfl
  · exact HahnSeries.coeff_eq_zero_of_lt_orderTop

/-- The constant coefficient identifies the Hahn residue field with R. -/
def hahnResidueEquiv : Residue realRationalHahnRing ≃+* ℝ := by
  change realRationalHahnRing ⧸ IsLocalRing.maximalIdeal realRationalHahnRing ≃+* ℝ
  rw [← hahnConstantCoefficient_ker]
  exact RingHom.quotientKerEquivOfSurjective hahnConstantCoefficient_surjective

@[instance_reducible]
def hahnLinearOrder : LinearOrder RealRationalHahn :=
  inferInstanceAs (LinearOrder (Lex RealRationalHahn))

set_option linter.style.haveILetI false in
theorem hahnIsStrictOrderedRing :
    letI := hahnLinearOrder
    IsStrictOrderedRing RealRationalHahn :=
  inferInstanceAs (IsStrictOrderedRing (Lex RealRationalHahn))

set_option linter.style.haveILetI false in
/-- The Hahn valuation ring is the convex hull of the constant
real series in the lexicographic order. -/
theorem hahnRing_iff_between_real_constants (x : RealRationalHahn) :
    letI := hahnLinearOrder
    x ∈ realRationalHahnRing ↔ ∃ a b : ℝ, HahnSeries.single 0 a ≤ x ∧ x ≤ HahnSeries.single 0 b := by
  letI := hahnLinearOrder
  rw [mem_realRationalHahnRing_iff]
  constructor
  · intro hx
    let a := x.coeff 0 - 1
    let b := x.coeff 0 + 1
    have hBelow (q : ℚ) (hq : q < 0) : x.coeff q = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hq).trans_le hx)
    have ha : HahnSeries.single (0 : ℚ) a < x :=
      (HahnSeries.lt_iff (toLex (HahnSeries.single (0 : ℚ) a)) (toLex x)).mpr
        ⟨0, fun q hq => (HahnSeries.coeff_single_of_ne hq.ne).trans (hBelow q hq).symm, by
          change (HahnSeries.single (0 : ℚ) a).coeff 0 < x.coeff 0
          rw [HahnSeries.coeff_single_same]
          exact sub_lt_self _ zero_lt_one⟩
    have hb : x < HahnSeries.single (0 : ℚ) b :=
      (HahnSeries.lt_iff (toLex x) (toLex (HahnSeries.single (0 : ℚ) b))).mpr
        ⟨0, fun q hq => (hBelow q hq).trans (HahnSeries.coeff_single_of_ne hq.ne).symm, by
          change x.coeff 0 < (HahnSeries.single (0 : ℚ) b).coeff 0
          rw [HahnSeries.coeff_single_same]
          exact lt_add_of_pos_right _ zero_lt_one⟩
    exact ⟨a, b, ha.le, hb.le⟩
  · rintro ⟨a, b, ha, hb⟩
    by_contra! hn
    have hx : x ≠ 0 := by
      intro h0
      rw [h0, HahnSeries.orderTop_zero] at hn
      exact not_top_lt hn
    have hq : x.order < 0 := by
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx] at hn
      exact WithTop.coe_lt_coe.mp hn
    have hBelow (q : ℚ) (hq' : q < x.order) : x.coeff q = 0 := by
      apply HahnSeries.coeff_eq_zero_of_lt_orderTop
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx]
      exact WithTop.coe_lt_coe.mpr hq'
    have hc := HahnSeries.leadingCoeff_ne_zero.mpr hx
    rcases lt_or_gt_of_ne hc with hn' | hp
    · apply not_lt_of_ge ha
      apply (HahnSeries.lt_iff (toLex x) (toLex (HahnSeries.single (0 : ℚ) a))).mpr
      refine ⟨x.order, fun q hq' => (hBelow q hq').trans
        (HahnSeries.coeff_single_of_ne (hq'.trans hq).ne).symm, ?_⟩
      change x.coeff x.order < (HahnSeries.single (0 : ℚ) a).coeff x.order
      rw [HahnSeries.coeff_single_of_ne hq.ne, ← HahnSeries.leadingCoeff_eq]
      exact hn'
    · apply not_lt_of_ge hb
      apply (HahnSeries.lt_iff (toLex (HahnSeries.single (0 : ℚ) b)) (toLex x)).mpr
      refine ⟨x.order, fun q hq' => (HahnSeries.coeff_single_of_ne (hq'.trans hq).ne).trans
        (hBelow q hq').symm, ?_⟩
      change (HahnSeries.single (0 : ℚ) b).coeff x.order < x.coeff x.order
      rw [HahnSeries.coeff_single_of_ne hq.ne, ← HahnSeries.leadingCoeff_eq]
      exact hp

set_option linter.style.haveILetI false in
theorem hahnRing_isOrderConvex : letI := hahnLinearOrder; IsOrderConvex realRationalHahnRing := by
  letI := hahnLinearOrder
  constructor
  intro a ha b hb x hx
  obtain ⟨r, _, hr, _⟩ := (hahnRing_iff_between_real_constants a).mp ha
  obtain ⟨_, s, _, hs⟩ := (hahnRing_iff_between_real_constants b).mp hb
  exact (hahnRing_iff_between_real_constants x).mpr ⟨r, s, hr.trans hx.1, hx.2.trans hs⟩

theorem hahnRing_nontrivially_valued : realRationalHahnRing.valuation.IsNontrivial := by
  apply (Valuation.isNontrivial_iff_exists_lt_one _).mpr
  let t : RealRationalHahn := HahnSeries.single (1 : ℚ) 1
  have ht : t ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mp (by
    simp only [t, HahnSeries.leadingCoeff_of_single]
    exact one_ne_zero)
  refine ⟨t, ht, ?_⟩
  rw [← map_one realRationalHahnRing.valuation, realRationalHahn_valuation_lt_iff,
    HahnSeries.orderTop_one]
  change (0 : WithTop ℚ) < (HahnSeries.single (1 : ℚ) (1 : ℝ)).orderTop
  rw [HahnSeries.orderTop_single one_ne_zero]
  exact WithTop.coe_lt_coe.mpr (zero_lt_one : (0 : ℚ) < 1)

private theorem hahn_single_inv (q : ℚ) {c : ℝ} (hc : c ≠ 0) :
    (HahnSeries.single q c)⁻¹ = HahnSeries.single (-q) c⁻¹ := by
  have hs : HahnSeries.single q c ≠ 0 :=
    HahnSeries.leadingCoeff_ne_zero.mp (by rwa [HahnSeries.leadingCoeff_of_single])
  symm
  apply (mul_eq_one_iff_eq_inv₀ hs).mp
  rw [HahnSeries.single_mul_single, neg_add_cancel, inv_mul_cancel₀ hc, HahnSeries.single_zero_one]

private theorem hahn_single_zpow (q : ℚ) {c : ℝ} (hc : c ≠ 0) (n : ℤ) :
    HahnSeries.single q c ^ n = HahnSeries.single ((n : ℚ) * q) (c ^ n) := by
  cases n with
  | ofNat n =>
    change HahnSeries.single q c ^ (n : ℤ) = HahnSeries.single ((n : ℤ) * (q : ℚ)) (c ^ (n : ℤ))
    rw [zpow_natCast, zpow_natCast, HahnSeries.single_pow, nsmul_eq_mul, Int.cast_natCast]
  | negSucc n =>
    rw [zpow_negSucc, HahnSeries.single_pow, hahn_single_inv _ (pow_ne_zero _ hc),
      zpow_negSucc, nsmul_eq_mul, Int.cast_negSucc, neg_mul, Nat.cast_add, Nat.cast_one]

set_option linter.style.haveILetI false in
private theorem hahn_single_pos (q : ℚ) {c : ℝ} (hc : 0 < c) :
    letI := hahnLinearOrder
    0 < HahnSeries.single q c := by
  letI := hahnLinearOrder
  change 0 < toLex (HahnSeries.single q c)
  apply HahnSeries.leadingCoeff_pos_iff.mp
  change 0 < (HahnSeries.single q c).leadingCoeff
  rwa [HahnSeries.leadingCoeff_of_single]

set_option linter.style.haveILetI false in
/-- The RV order compares the first coefficient at which the two
monomials differ. In a fixed sign branch this reverses the comparison
of exponents on the positive branch. -/
theorem hahn_rv_single_lt_iff {q r : ℚ} {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    letI := hahnLinearOrder
    letI := hahnIsStrictOrderedRing
    letI := rvLinearOrder realRationalHahnRing hahnRing_isOrderConvex
    rv realRationalHahnRing (HahnSeries.single q c) <
      rv realRationalHahnRing (HahnSeries.single r d) ↔
      (q < r ∧ c < 0) ∨ (r < q ∧ 0 < d) ∨ (q = r ∧ c < d) := by
  letI := hahnLinearOrder
  letI := hahnIsStrictOrderedRing
  letI := rvLinearOrder realRationalHahnRing hahnRing_isOrderConvex
  rw [rv_lt_rv_iff realRationalHahnRing hahnRing_isOrderConvex, ne_eq, hahn_rv_single_eq_iff hc hd,
    ← sub_pos]
  have hPos (x : RealRationalHahn) : 0 < x ↔ 0 < x.leadingCoeff :=
    (HahnSeries.leadingCoeff_pos_iff (x := toLex x)).symm
  rw [hPos]
  rcases lt_trichotomy q r with h | rfl | h
  · have ho : (-(HahnSeries.single q c)).orderTop < (HahnSeries.single r d).orderTop := by
      rw [HahnSeries.orderTop_neg, HahnSeries.orderTop_single hc, HahnSeries.orderTop_single hd,
        WithTop.coe_lt_coe]
      exact h
    rw [sub_eq_add_neg, HahnSeries.leadingCoeff_add_eq_right ho, HahnSeries.leadingCoeff_neg,
      HahnSeries.leadingCoeff_of_single, neg_pos]
    simp [h, h.ne, h.not_gt]
  · rw [← HahnSeries.single_sub, HahnSeries.leadingCoeff_of_single, sub_pos]
    simp only [lt_irrefl, false_and, true_and, false_or]
    exact ⟨And.left, fun h => ⟨h, h.ne⟩⟩
  · have ho : (HahnSeries.single r d).orderTop < (HahnSeries.single q c).orderTop := by
      rw [HahnSeries.orderTop_single hc, HahnSeries.orderTop_single hd, WithTop.coe_lt_coe]
      exact h
    rw [HahnSeries.leadingCoeff_sub ho, HahnSeries.leadingCoeff_of_single]
    simp [h, h.ne', h.not_gt]

set_option linter.style.haveILetI false in
/-- The positive rational power of a Hahn monomial is determined by
the positive root characterizing that rational power. -/
theorem hahn_rationalPower_on_monomial (e q : ℚ) {c : ℝ} (hc : 0 < c) :
    letI := hahnLinearOrder
    ∀ {y : RealRationalHahn}, 0 < y →
      y ^ e.den = HahnSeries.single q c ^ e.num →
      y = HahnSeries.single (e * q) (c ^ (e : ℝ)) := by
  letI := hahnLinearOrder
  letI := hahnIsStrictOrderedRing
  intro y hy h
  let b := HahnSeries.single (e * q) (c ^ (e : ℝ))
  have hb : 0 < b := hahn_single_pos _ (Real.rpow_pos_of_pos hc _)
  apply (pow_left_inj₀ hy.le hb.le e.den_nz).mp
  rw [h, hahn_single_zpow _ hc.ne', HahnSeries.single_pow, nsmul_eq_mul]
  have hRat {F : Type} [Field F] [CharZero F] :
      (e : F) * (e.den : F) = (e.num : F) :=
    (eq_div_iff (Nat.cast_ne_zero.mpr e.den_nz)).mp (Rat.cast_def e)
  have hExp : (e.den : ℚ) * (e * q) = (e.num : ℚ) * q := by
    rw [← mul_assoc, mul_comm (e.den : ℚ) e]
    exact congrArg (fun t : ℚ => t * q) (by simpa only [Rat.cast_id] using (hRat (F := ℚ)))
  have hCoeff : (c ^ (e : ℝ)) ^ e.den = c ^ e.num := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, hRat (F := ℝ), Real.rpow_intCast]
  rw [hExp, hCoeff]

set_option linter.style.haveILetI false in
/-- The named RV power has the rational-power formula in Hahn coordinates. -/
theorem hahn_rv_rationalPower_on_positive_monomial (e q : ℚ) {c : ℝ} (hc : 0 < c) :
    letI := hahnLinearOrder
    letI := hahnIsStrictOrderedRing
    ∀ (g : PositiveField RealRationalHahn →* PositiveField RealRationalHahn)
      (P : RV0 realRationalHahnRing → RV0 realRationalHahnRing),
      AgreesWithFieldPower realRationalHahnRing g P →
      (∀ x : PositiveField RealRationalHahn, (g x).val ^ e.den = x.val ^ e.num) →
      hahnRVEquiv (P (rv realRationalHahnRing (HahnSeries.single q c))) =
        ((Multiplicative.ofAdd (e * q), Units.mk0 (c ^ (e : ℝ))
          (Real.rpow_pos_of_pos hc _).ne') : Multiplicative ℚ × ℝˣ) := by
  letI := hahnLinearOrder
  letI := hahnIsStrictOrderedRing
  intro g P hP hRoot
  let x : PositiveField RealRationalHahn := ⟨HahnSeries.single q c, hahn_single_pos q hc⟩
  change hahnRVEquiv (P (rv realRationalHahnRing x.val)) = _
  rw [hP x, hahnRVEquiv_rv, hahn_rationalPower_on_monomial e q hc (g x).property (hRoot x)]
  exact hahnLeadingCoordinates_single (e * q) (Units.mk0 _ (Real.rpow_pos_of_pos hc _).ne')

open FirstOrder

universe u v

/-- The analytic input of Example 2.8 in the language with inverse and
positive root symbols. Elementarity is DMM (1994), Corollary 2.11,
and the universal presentation uses Theorem 2.14. The growth and
exponent fields record the two restrictions cited in the example. -/
structure RestrictedAnalyticHahnFacts (L : Language.{u, v})
    [L.Structure ℝ] [L.Structure RealRationalHahn] where
  elementary : ℝ ↪ₑ[L] RealRationalHahn
  constants : ∀ r, elementary r = HahnSeries.single 0 r
  universal : (L.completeTheory ℝ).IsUniversal
  quantifierElimination : EliminatesQuantifiers (L.completeTheory ℝ)
  polynomialBounded : ∀ f : ℝ → ℝ, (Set.univ : Set ℝ).Definable₂ L (fieldGraph Set.univ f) →
    ∃ (n : ℕ) (b : ℝ), ∀ x > b, |f x| ≤ x ^ n
  rationalPowers : ∀ f : PositiveField ℝ →* PositiveField ℝ,
    (∅ : Set ℝ).Definable₂ L (powerGraph f) →
    ∃ q : ℚ, ∀ x : PositiveField ℝ, (f x : ℝ) = (x : ℝ) ^ (q : ℝ)

variable {L : Language.{u, v}} [L.Structure ℝ] [L.Structure RealRationalHahn]

theorem RestrictedAnalyticHahnFacts.hahnModels (d : RestrictedAnalyticHahnFacts L) :
    RealRationalHahn ⊨ L.completeTheory ℝ := by
  constructor
  intro φ hφ
  exact (d.elementary.map_sentence φ).mp hφ

set_option linter.style.haveILetI false in
/-- The analytic Hahn pair has the canonical T-convex expansion given
the convex-hull and residue-matching inputs of van den Dries–Lewenberg. -/
theorem existsUnique_restrictedAnalyticHahnExpansion
    (d : RestrictedAnalyticHahnFacts L)
    [L.Structure (Residue realRationalHahnRing)]
    [TopologicalSpace RealRationalHahn] [TopologicalSpace (Residue realRationalHahnRing)] :
    letI := hahnLinearOrder
    letI := hahnIsStrictOrderedRing
    ∀ (g : ℚ → PositiveField RealRationalHahn →* PositiveField RealRationalHahn),
      Residue realRationalHahnRing ⊨ L.completeTheory ℝ →
      IsTConvex L realRationalHahnRing →
      MatchesContinuousFunctions L realRationalHahnRing →
      ∀ gResidue : ℚ → Residue realRationalHahnRing → Residue realRationalHahnRing,
        (∀ e, ResidueCompatible realRationalHahnRing (fun x => g e (clampForPower x)) (gResidue e)) →
        (∀ e, gResidue e 1 = 1) →
        ∃! P : ℚ → RV0 realRationalHahnRing → RV0 realRationalHahnRing,
          CanonicalTCVFModel realRationalHahnRing (L.completeTheory ℝ) g P := by
  letI := hahnLinearOrder
  letI := hahnIsStrictOrderedRing
  intro g hRes hConvex hMatch gRes hClamp hOne
  exact existsUnique_canonicalTCVFModel realRationalHahnRing (L.completeTheory ℝ) g
    d.hahnModels hRes hahnRing_nontrivially_valued hConvex hMatch gRes hClamp hOne

end GeneralizedEuler.Section2


