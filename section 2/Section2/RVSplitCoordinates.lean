module

public import Section2.RVVectorSpace
public import Section2.ResidueFiber
public import Section2.SortedStructure

/-! Coordinates for finite-sign separation in the RV reduct. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K}

/-- A multiplicative section with positive leading-term representatives. -/
structure RVValueSection (O : ValuationSubring K) where
  lift : O.ValueGroupˣ →* PositiveRV O
  value_lift : ∀ γ, positiveValueMap O (lift γ) = γ

namespace RVValueSection

variable (S : RVValueSection O)

def representative (γ : O.ValueGroupˣ) : RV0 O := positiveRVToRV0 O (S.lift γ)

theorem representative_pos (γ : O.ValueGroupˣ) : IsPositiveRV O (S.representative γ) :=
  positiveRVToRV0_pos O (S.lift γ)

theorem representative_ne_zero (γ : O.ValueGroupˣ) : S.representative γ ≠ 0 := by
  obtain ⟨x, hx⟩ := S.representative_pos γ
  exact hx ▸ (rv_eq_zero_iff O).not.mpr x.property.ne'

@[simp] theorem unsignedValue_representative (γ : O.ValueGroupˣ) :
    unsignedValue O (S.representative γ) = γ := by
  rw [← show (positiveValueMap O (S.lift γ) : O.ValueGroup) =
    unsignedValue O (S.representative γ) from positiveValueMap_coe O _, S.value_lift]

@[simp] theorem representative_one : S.representative 1 = 1 := by
  unfold representative
  rw [map_one, positiveRVToRV0_one]

@[simp] theorem representative_mul (γ δ : O.ValueGroupˣ) :
    S.representative (γ * δ) = S.representative γ * S.representative δ := by
  unfold representative
  rw [map_mul, positiveRVToRV0_mul]

/-- Zero uses the unit value as a dummy coordinate. Its residue
coordinate distinguishes it from all nonzero leading terms. -/
def valueCoordinate (t : RV0 O) : O.ValueGroupˣ := by
  classical
  exact if ht : t = 0 then 1 else Units.mk0 (unsignedValue O t)
    ((map_ne_zero (G₀ := RV0 O) (M₀' := O.ValueGroup) (unsignedValue O)).mpr ht)

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem valueCoordinate_zero : valueCoordinate (0 : RV0 O) = 1 := by
  simp [valueCoordinate]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem coe_valueCoordinate {t : RV0 O} (ht : t ≠ 0) :
    (valueCoordinate t : O.ValueGroup) = unsignedValue O t := by
  simp [valueCoordinate, ht]

def residueCoordinate (t : RV0 O) : Residue O :=
  rvResidue O (t / S.representative (valueCoordinate t))

def join (γ : O.ValueGroupˣ) (r : Residue O) : RV0 O := S.representative γ * residueRV O r

@[simp] theorem join_zero (γ : O.ValueGroupˣ) : S.join γ 0 = 0 := by
  simp only [join, residueRV_zero, mul_zero (M₀ := RV0 O)]

@[simp] theorem join_one (r : Residue O) : S.join 1 r = residueRV O r := by
  rw [join, S.representative_one, one_mul (M := RV0 O)]

theorem join_ne_zero (γ : O.ValueGroupˣ) {r : Residue O} (hr : r ≠ 0) :
    S.join γ r ≠ 0 := by
  have hr' : residueRV O r ≠ 0 := fun h => hr (residueRV_injective O (h.trans (residueRV_zero O).symm))
  exact mul_ne_zero (S.representative_ne_zero γ) hr'

theorem join_coordinates (t : RV0 O) : S.join (valueCoordinate t) (S.residueCoordinate t) = t := by
  unfold join residueCoordinate
  by_cases ht : t = 0
  · subst t
    rw [zero_div (G₀ := RV0 O), ← residueRV_zero O, rvResidue_residueRV, residueRV_zero,
      mul_zero (M₀ := RV0 O)]
  · let γ := valueCoordinate t
    have hv : unsignedValue O t = unsignedValue O (S.representative γ) :=
      (coe_valueCoordinate ht).symm.trans (S.unsignedValue_representative γ).symm
    have h := div_mem_residueRV_of_equal_unsignedValue O hv
    rw [residueRV_rvResidue_of_mem_range O h, mul_comm (G := RV0 O),
      div_mul_cancel₀ (G₀ := RV0 O) _ (S.representative_ne_zero γ)]

theorem valueCoordinate_join (γ : O.ValueGroupˣ) {r : Residue O} (hr : r ≠ 0) :
    valueCoordinate (S.join γ r) = γ := by
  apply Units.ext
  rw [coe_valueCoordinate (S.join_ne_zero γ hr), join, map_mul,
    S.unsignedValue_representative, unsignedValue_residueRV_of_ne_zero O hr, mul_one]

theorem valueCoordinate_join_of_valid (γ : O.ValueGroupˣ) (r : Residue O)
    (h : r = 0 → γ = 1) : valueCoordinate (S.join γ r) = γ := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [S.join_zero, valueCoordinate_zero, h rfl]
  · exact S.valueCoordinate_join γ hr

theorem residueCoordinate_join (γ : O.ValueGroupˣ) (r : Residue O) :
    S.residueCoordinate (S.join γ r) = r := by
  rcases eq_or_ne r 0 with rfl | hr
  · unfold residueCoordinate
    rw [S.join_zero, zero_div (G₀ := RV0 O), ← residueRV_zero O, rvResidue_residueRV]
  · unfold residueCoordinate
    rw [S.valueCoordinate_join γ hr, join, mul_comm (G := RV0 O) (S.representative γ) (residueRV O r),
      div_eq_mul_inv (G := RV0 O), mul_assoc (G := RV0 O), mul_inv_cancel₀ (G₀ := RV0 O) (S.representative_ne_zero γ),
      mul_one (M := RV0 O), rvResidue_residueRV]

@[simp] theorem residueCoordinate_zero : S.residueCoordinate 0 = 0 := by
  rw [← S.join_zero 1, S.residueCoordinate_join]

theorem residueCoordinate_eq_zero {t : RV0 O} : S.residueCoordinate t = 0 ↔ t = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ S.residueCoordinate_zero⟩
  rw [← S.join_coordinates t, h, S.join_zero]

/-- Signed residue and unsigned value recover all RV elements. The
pair `(1, 0)` is the single code for zero. -/
def coordinates : RV0 O ≃ {p : O.ValueGroupˣ × Residue O // p.2 = 0 → p.1 = 1} where
  toFun t := ⟨(valueCoordinate t, S.residueCoordinate t), fun h => by
    rw [S.residueCoordinate_eq_zero] at h
    rw [h, valueCoordinate_zero]⟩
  invFun p := S.join p.val.1 p.val.2
  left_inv := S.join_coordinates
  right_inv p := Subtype.ext (Prod.ext (by
    change valueCoordinate (S.join p.val.1 p.val.2) = p.val.1
    rcases eq_or_ne p.val.2 0 with h | h
    · rw [h, S.join_zero, valueCoordinate_zero, p.property h]
    · exact S.valueCoordinate_join _ h) (S.residueCoordinate_join _ _))

theorem join_mul (γ δ : O.ValueGroupˣ) (r s : Residue O) :
    S.join γ r * S.join δ s = S.join (γ * δ) (r * s) := by
  simp only [join, representative_mul, residueRV_mul]
  exact mul_mul_mul_comm (G := RV0 O) _ _ _ _

theorem residueCoordinate_mul (t u : RV0 O) :
    S.residueCoordinate (t * u) = S.residueCoordinate t * S.residueCoordinate u := by
  nth_rw 1 [← S.join_coordinates t, ← S.join_coordinates u]
  rw [S.join_mul, S.residueCoordinate_join]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem valueCoordinate_mul {t u : RV0 O} (ht : t ≠ 0) (hu : u ≠ 0) :
    valueCoordinate (t * u) = valueCoordinate t * valueCoordinate u := by
  apply Units.ext
  rw [Units.val_mul, coe_valueCoordinate (mul_ne_zero ht hu), map_mul, coe_valueCoordinate ht,
    coe_valueCoordinate hu]

@[simp] theorem residueCoordinate_residueRV (r : Residue O) :
    S.residueCoordinate (residueRV O r) = r := by
  rw [← S.join_one, S.residueCoordinate_join]

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem valueCoordinate_residueRV (r : Residue O) :
    valueCoordinate (residueRV O r) = 1 := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [residueRV_zero, valueCoordinate_zero]
  · have hne : residueRV O r ≠ 0 := fun h =>
      hr (residueRV_injective O (h.trans (residueRV_zero O).symm))
    exact Units.ext ((coe_valueCoordinate hne).trans (unsignedValue_residueRV_of_ne_zero O hr))

include S in
theorem valueCoordinate_eq_one_iff {t : RV0 O} :
    valueCoordinate t = 1 ↔ t ∈ Set.range (residueRV O) := by
  constructor
  · intro h
    refine ⟨S.residueCoordinate t, ?_⟩
    rw [← S.join_one, ← h, S.join_coordinates]
  · rintro ⟨r, rfl⟩
    exact valueCoordinate_residueRV r

theorem unsignedValue_eq_one_iff_coordinates {t : RV0 O} :
    unsignedValue O t = 1 ↔ valueCoordinate t = 1 ∧ S.residueCoordinate t ≠ 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [map_zero, zero_ne_one, valueCoordinate_zero, S.residueCoordinate_zero, ne_eq, not_true_eq_false,
      and_false]
  · exact ⟨fun h => ⟨Units.ext ((coe_valueCoordinate ht).trans h), S.residueCoordinate_eq_zero.not.mpr ht⟩,
      fun h => (coe_valueCoordinate ht).symm.trans (congrArg Units.val h.1)⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem valueCoordinate_inv (t : RV0 O) : valueCoordinate t⁻¹ = (valueCoordinate t)⁻¹ := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [inv_zero (G₀ := RV0 O), valueCoordinate_zero, inv_one]
  apply Units.ext
  rw [Units.val_inv_eq_inv_val, coe_valueCoordinate (inv_ne_zero (G₀ := RV0 O) ht),
    coe_valueCoordinate ht, map_inv₀ (G₀ := RV0 O) (G₀' := O.ValueGroup) (unsignedValue O)]

theorem join_inv (γ : O.ValueGroupˣ) (r : Residue O) :
    (S.join γ r)⁻¹ = S.join γ⁻¹ r⁻¹ := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [inv_zero, S.join_zero, inv_zero (G₀ := RV0 O), S.join_zero]
  have h : S.join γ r * S.join γ⁻¹ r⁻¹ = 1 := by
    rw [S.join_mul, mul_inv_cancel, mul_inv_cancel₀ hr, S.join_one, residueRV_one]
  apply rv_mul_left_cancel O (S.join_ne_zero γ hr)
  rw [mul_inv_cancel₀ (G₀ := RV0 O) (S.join_ne_zero γ hr), h]

theorem residueCoordinate_inv (t : RV0 O) :
    S.residueCoordinate t⁻¹ = (S.residueCoordinate t)⁻¹ := by
  nth_rw 1 [← S.join_coordinates t]
  rw [S.join_inv, S.residueCoordinate_join]

set_option linter.style.haveILetI false in
theorem join_le_join_same_value (hO : IsOrderConvex O) (γ : O.ValueGroupˣ) (r s : Residue O) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    S.join γ r ≤ S.join γ s ↔ r ≤ s := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  have hp := (isPositiveRV_iff_pos O hO).mp (S.representative_pos γ)
  exact ((rv_mul_left_strictMono O hO hp).comp (residueRV_strictMono O hO)).le_iff_le

set_option linter.style.haveILetI false in
theorem join_lt_join_same_value (hO : IsOrderConvex O) (γ : O.ValueGroupˣ) (r s : Residue O) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    S.join γ r < S.join γ s ↔ r < s := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  rw [lt_iff_not_ge, S.join_le_join_same_value hO, not_le]

set_option linter.style.haveILetI false in
theorem join_pos_iff (hO : IsOrderConvex O) (γ : O.ValueGroupˣ) (r : Residue O) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    0 < S.join γ r ↔ 0 < r := by
  letI := rvLinearOrder O hO
  rw [← S.join_zero γ]
  exact S.join_lt_join_same_value hO γ 0 r

set_option linter.style.haveILetI false in
theorem join_neg_iff (hO : IsOrderConvex O) (γ : O.ValueGroupˣ) (r : Residue O) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    S.join γ r < 0 ↔ r < 0 := by
  letI := rvLinearOrder O hO
  rw [← S.join_zero γ]
  exact S.join_lt_join_same_value hO γ r 0

set_option linter.style.haveILetI false in
theorem join_le_join_positive (hO : IsOrderConvex O) (γ δ : O.ValueGroupˣ) (r s : Residue O)
    (hr : letI := residueLinearOrder O hO; 0 < r) (hs : letI := residueLinearOrder O hO; 0 < s) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    S.join γ r ≤ S.join δ s ↔ (γ : O.ValueGroup) < δ ∨ (γ = δ ∧ r ≤ s) := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  have hv (ζ : O.ValueGroupˣ) {x : Residue O} (hx : x ≠ 0) :
      unsignedValue O (S.join ζ x) = ζ := by
    rw [join, map_mul, S.unsignedValue_representative, unsignedValue_residueRV_of_ne_zero O hx, mul_one]
  rcases lt_trichotomy (γ : O.ValueGroup) (δ : O.ValueGroup) with h | h | h
  · have hv' : unsignedValue O (S.join γ r) < unsignedValue O (S.join δ s) := by
      rwa [hv γ hr.ne', hv δ hs.ne']
    exact iff_of_true (rv_lt_of_value_lt_positive O hO ((S.join_pos_iff hO δ s).mpr hs) hv').le (.inl h)
  · obtain rfl : γ = δ := Units.ext h
    simpa only [lt_self_iff_false, true_and, false_or] using S.join_le_join_same_value hO γ r s
  · have hv' : unsignedValue O (S.join δ s) < unsignedValue O (S.join γ r) := by
      rwa [hv γ hr.ne', hv δ hs.ne']
    exact iff_of_false (rv_lt_of_value_lt_positive O hO ((S.join_pos_iff hO γ r).mpr hr) hv').not_ge
      (fun hh => hh.elim h.not_gt (fun h' => h.ne (congrArg Units.val h'.1).symm))

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem residueRV_neg_one_eq (O : ValuationSubring K) :
    residueRV O (-1 : Residue O) = rv O (-1) := by
  have h : IsLocalRing.residue O (-1 : O) ≠ 0 := by simp
  simpa only [map_neg, map_one, NegMemClass.coe_neg, OneMemClass.coe_one] using
    residueRV_residue_of_ne_zero O (-1 : O) h

theorem neg_join (γ : O.ValueGroupˣ) (r : Residue O) :
    rv O (-1) * S.join γ r = S.join γ (-r) := by
  rw [← residueRV_neg_one_eq, ← S.join_one (-1), S.join_mul, one_mul, neg_one_mul]

set_option linter.style.haveILetI false in
private theorem rv_neg_anti_order (hO : IsOrderConvex O) (x y : RV0 O) :
    letI := rvLinearOrder O hO
    rv O (-1) * x ≤ rv O (-1) * y ↔ y ≤ x := by
  letI := rvLinearOrder O hO
  obtain ⟨a, rfl⟩ := rv_surjective O x
  obtain ⟨b, rfl⟩ := rv_surjective O y
  have hv : rv O (-1) ≠ 0 := (rv_eq_zero_iff O).not.mpr (neg_ne_zero.mpr one_ne_zero)
  have h (a : K) : rv O (-1) * rv O a = rv O (-a) := by
    rw [← map_mul (rv O), neg_one_mul]
  rw [h a, h b, rv_le_rv_iff O hO, rv_le_rv_iff O hO]
  refine or_congr neg_le_neg_iff ?_
  rw [← h a, ← h b]
  exact ⟨fun he => (rv_mul_left_cancel O hv he).symm, fun he => congrArg (fun t => rv O (-1) * t) he.symm⟩

set_option linter.style.haveILetI false in
theorem join_le_join_negative (hO : IsOrderConvex O) (γ δ : O.ValueGroupˣ) (r s : Residue O)
    (hr : letI := residueLinearOrder O hO; r < 0) (hs : letI := residueLinearOrder O hO; s < 0) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    S.join γ r ≤ S.join δ s ↔ (δ : O.ValueGroup) < γ ∨ (γ = δ ∧ r ≤ s) := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  letI := residue_isOrderedRing O hO
  have horder := rv_neg_anti_order hO (S.join δ s) (S.join γ r)
  rw [S.neg_join, S.neg_join] at horder
  rw [← horder, S.join_le_join_positive hO δ γ (-s) (-r) (neg_pos.mpr hs) (neg_pos.mpr hr),
    neg_le_neg_iff, eq_comm (a := δ)]

/-- A residue operation uses only the residue coordinates when every
input has unit value. On all other coordinate tuples it is clamped to zero. -/
theorem extendResidueOperation_join {n : ℕ} (f : (Fin n → Residue O) → Residue O)
    (γ : Fin n → O.ValueGroupˣ) (r : Fin n → Residue O) (h : ∀ i, r i = 0 → γ i = 1) :
    extendResidueOperation O f (fun i => S.join (γ i) (r i)) =
      if ∀ i, γ i = 1 then residueRV O (f r) else 0 := by
  classical
  have hvalid (i : Fin n) :
      S.join (γ i) (r i) ∈ Set.range (residueRV O) ↔ γ i = 1 := by
    rw [← S.valueCoordinate_eq_one_iff, S.valueCoordinate_join_of_valid (γ i) (r i) (h i)]
  by_cases hg : ∀ i, γ i = 1
  · have heq : (fun i => S.join (γ i) (r i)) = residueRV O ∘ r := by
      funext i
      exact (congrArg (fun g => S.join g (r i)) (hg i)).trans (S.join_one (r i))
    rw [ite_eq_left hg, heq, extendResidueOperation_on_residue]
  · rw [ite_eq_right hg]
    push Not at hg
    obtain ⟨i, hi⟩ := hg
    exact extendResidueOperation_off_residue O f ⟨i, (hvalid i).not.mpr hi⟩

set_option linter.style.haveILetI false in
theorem leadingTermPower_join_positive (hO : IsOrderConvex O)
    {g : PositiveField K →* PositiveField K} {P : RV0 O → RV0 O}
    (hP : AgreesWithFieldPower O g P)
    (hunit : ∀ x : PositiveField K, O.valuation (x : K) = 1 → O.valuation (g x : K) = 1)
    (p : O.ValueGroupˣ → O.ValueGroupˣ)
    (hsection : ∀ γ, P (S.representative γ) = S.representative (p γ))
    (γ : O.ValueGroupˣ) (r : Residue O) (hr : letI := residueLinearOrder O hO; 0 < r) :
    P (S.join γ r) = S.join (p γ) (rvResidue O (P (residueRV O r))) := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  have hpos : IsPositiveRV O (residueRV O r) := by
    apply (isPositiveRV_iff_pos O hO).mpr
    simpa only [residueRV_zero] using residueRV_strictMono O hO hr
  have hu : unsignedValue O (P (residueRV O r)) = 1 := by
    obtain ⟨x, hx⟩ := hpos
    have hv : O.valuation (x : K) = 1 := by
      rw [← unsignedValue_rv, hx, unsignedValue_residueRV_of_ne_zero O hr.ne']
    rw [← hx, hP x, unsignedValue_rv]
    exact hunit x hv
  have hm : P (residueRV O r) ∈ Set.range (residueRV O) := by
    rw [range_residueRV]
    exact .inr hu
  change P (S.representative γ * residueRV O r) =
    S.representative (p γ) * residueRV O (rvResidue O (P (residueRV O r)))
  rw [leadingTermPower_mul O hP (S.representative_pos γ) hpos, hsection,
    residueRV_rvResidue_of_mem_range O hm]

set_option linter.style.haveILetI false in
theorem leadingTermPower_join_nonpositive (hO : IsOrderConvex O) (P : RV0 O → RV0 O)
    (hclamp : ∀ t, ¬IsPositiveRV O t → P t = 0)
    (γ : O.ValueGroupˣ) (r : Residue O) (hr : letI := residueLinearOrder O hO; r ≤ 0) :
    P (S.join γ r) = 0 := by
  letI := residueLinearOrder O hO
  apply hclamp
  intro hp
  exact hr.not_gt ((S.join_pos_iff hO γ r).mp ((isPositiveRV_iff_pos O hO).mp hp))

end RVValueSection

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Choose the positive value representatives compatibly with the
original positive RV subspace and every named exponent. -/
theorem exists_rvValueSection_preserving_base_and_powers {E : Type*} [Field E]
    (O : ValuationSubring K) (g : E → PositiveField K →* PositiveField K)
    (P : E → RV0 O → RV0 O) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
    (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
    (hmul : ∀ e d x, g (e * d) x = g e (g d x))
    (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1) :
    letI := positiveRVModule O g P hP hzero hone hadd hmul
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    ∀ W : Submodule E (Additive (PositiveRV O)), ∃ S : RVValueSection O,
      (∀ γ : O.ValueGroupˣ, Additive.ofMul γ ∈ W.map
        (positiveValueLinearMap O g P hP hzero hone hadd hmul hunit) →
          Additive.ofMul (S.lift γ) ∈ W) ∧
      ∀ (e : E) (γ : O.ValueGroupˣ),
        P e (S.representative γ) = S.representative (e • Additive.ofMul γ).toMul := by
  letI := positiveRVModule O g P hP hzero hone hadd hmul
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  intro W
  let v := positiveValueLinearMap O g P hP hzero hone hadd hmul hunit
  have hv : Function.Surjective v :=
    positiveValueLinearMap_surjective O g P hP hzero hone hadd hmul hunit
  obtain ⟨s, hs, hW⟩ := exists_linearSection_preserving_base (E := E)
    (G := Additive (PositiveRV O)) (V := Additive (O.ValueGroupˣ)) v hv W
  let lift : O.ValueGroupˣ →* PositiveRV O :=
    { toFun := fun γ => (s (Additive.ofMul γ)).toMul
      map_one' := congrArg Additive.toMul (map_zero s)
      map_mul' := fun γ δ => congrArg Additive.toMul (map_add s (Additive.ofMul γ) (Additive.ofMul δ)) }
  let S : RVValueSection O :=
    ⟨lift, fun γ => by
      have h := DFunLike.congr_fun hs (Additive.ofMul γ)
      change v (s (Additive.ofMul γ)) = Additive.ofMul γ at h
      rw [positiveValueLinearMap_apply] at h
      exact congrArg Additive.toMul h⟩
  refine ⟨S, fun γ hγ => hW (Additive.ofMul γ) hγ, ?_⟩
  intro e γ
  change P e (positiveRVToRV0 O (s (Additive.ofMul γ)).toMul) =
    positiveRVToRV0 O (s (e • Additive.ofMul γ)).toMul
  rw [map_smul, positiveRVToRV0_smul O g P hP hzero hone hadd hmul]

end GeneralizedEuler.Section2
