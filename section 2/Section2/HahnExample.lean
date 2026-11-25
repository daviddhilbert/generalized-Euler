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


