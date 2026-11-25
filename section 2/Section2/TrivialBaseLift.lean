module

public import Section2.ImmediateExtension

/-! The leading-term calculation over a trivially valued base in the
reviewed proof of Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

def positiveAbs (x : K) (hx : x ≠ 0) : PositiveField K :=
  ⟨|x|, abs_pos.mpr hx⟩

/-- The leading-term input from Freni, Corollary 3.3.13, for a specified
one-generator elementary extension and its fixed field powers. -/
def LeadingTermMonomialTransfer (g : E → PositiveField K →* PositiveField K)
    (A B : Subfield K) (a : K) : Prop :=
  ∀ y ∈ B, O.valuation y ∉ O.valuation '' (A : Set K) →
    ∃ (c : K) (_ : c ∈ A) (d : K) (_ : d ∈ A) (hc : a - c ≠ 0) (e : E),
      rv O y = rv O (d * (g e (positiveAbs (a - c) hc) : K))

/-- The value-group conclusion of Proposition 2.21 from the approved
leading-term input. Equal positive values remain equal after taking a
fixed field power. -/
theorem exists_translate_of_new_value
    {g : E → PositiveField K →* PositiveField K} {A B : Subfield K} {a y : K}
    (hFreni : LeadingTermMonomialTransfer O g A B a)
    (hpowBase : ∀ e (x : PositiveField K), (x : K) ∈ A → (g e x : K) ∈ A)
    (hpowValue : ∀ e (x z : PositiveField K),
      O.valuation (x : K) = O.valuation (z : K) →
      O.valuation (g e x : K) = O.valuation (g e z : K))
    (hyB : y ∈ B) (hy : O.valuation y ∉ O.valuation '' (A : Set K)) :
    ∃ c ∈ A, O.valuation (a - c) ∉ O.valuation '' (A : Set K) := by
  obtain ⟨c, hc, d, hd, hne, e, hr⟩ := hFreni y hyB hy
  refine ⟨c, hc, ?_⟩
  rintro ⟨b, hb, hbval⟩
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hbval
    exact ((map_ne_zero O.valuation).mpr hne) hbval.symm
  let x := positiveAbs (a - c) hne
  let z := positiveAbs b hb0
  change b ∈ A at hb
  have hz : (z : K) ∈ A := by
    change |b| ∈ A
    rcases le_or_gt 0 b with h | h
    · simpa only [abs_of_nonneg h] using hb
    · simpa only [abs_of_neg h] using A.neg_mem hb
  have hv : O.valuation (x : K) = O.valuation (z : K) := by
    change O.valuation |a - c| = O.valuation |b|
    rw [valuation_abs, valuation_abs, hbval]
  refine hy ⟨d * (g e z : K), A.mul_mem hd (hpowBase e z hz), ?_⟩
  have h := congrArg (unsignedValue O) hr
  rw [unsignedValue_rv, unsignedValue_rv, map_mul,
    hpowValue e x z hv] at h
  rw [map_mul]
  exact h.symm

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rv_translation_of_infinitesimal {a c : K}
    (ha : O.valuation a < 1) (hc : O.valuation c = 1) :
    rv O (a - c) = rv O (-c) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  apply (rv_eq_rv_iff_valuation O (neg_ne_zero.mpr hc0)).mpr
  rw [sub_neg_eq_add, sub_add_cancel, O.valuation.map_neg, hc]
  exact ha

/-- For a positive infinitesimal generator over a trivially valued base,
every nonzero leading term is an old leading term times a power of the
specified new leading term. -/
theorem trivialBase_leadingTerm [Ring E]
    {g : E → PositiveField K →* PositiveField K} {P : E → RV0 O → RV0 O}
    {A B : Subfield K} (hO : IsOrderConvex O) (a : PositiveField K)
    (haB : (a : K) ∈ B) (ha : O.valuation (a : K) < 1)
    (htriv : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1)
    (hbase : ∀ e (x : PositiveField K), (x : K) ∈ A → (g e x : K) ∈ A)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hone : g 1 a = a) (hadd : ∀ e d, g (e + d) a = g e a * g d a)
    (hFreni : LeadingTermMonomialTransfer O g A B a)
    {x : K} (hxB : x ∈ B) (hx0 : x ≠ 0) :
    ∃ d ∈ A, ∃ e : E, rv O x = rv O d * P e (rv O a) := by
  unfold AgreesWithFieldPower at hP
  have hnew (y : K) (hyB : y ∈ B) (hy0 : y ≠ 0) (hy1 : O.valuation y ≠ 1) :
      ∃ d ∈ A, ∃ e : E, rv O y = rv O d * rv O (g e a : K) := by
    have hy : O.valuation y ∉ O.valuation '' (A : Set K) := by
      rintro ⟨z, hz, hzy⟩
      by_cases hz0 : z = 0
      · rw [hz0, map_zero] at hzy
        exact ((map_ne_zero O.valuation).mpr hy0) hzy.symm
      · exact hy1 (hzy.symm.trans (htriv z hz hz0))
    obtain ⟨c, hc, d, hd, hn, e, he⟩ := hFreni y hyB hy
    by_cases hc0 : c = 0
    · subst c
      have ha' : positiveAbs ((a : K) - 0) hn = a :=
        Subtype.ext (by simp only [positiveAbs, sub_zero, abs_of_pos a.property])
      rw [ha', map_mul] at he
      exact ⟨d, hd, e, he⟩
    · have hrv : rv O |(a : K) - c| = rv O |c| := by
        have h := congrArg (rvAbs O hO) (rv_translation_of_infinitesimal O ha (htriv c hc hc0))
        simpa only [rvAbs_rv, abs_neg] using h
      let p := positiveAbs c hc0
      have hp : (p : K) ∈ A := by
        change |c| ∈ A
        rcases le_or_gt 0 c with h | h
        · simpa only [abs_of_nonneg h] using hc
        · simpa only [abs_of_neg h] using A.neg_mem hc
      have hpow : rv O (g e (positiveAbs ((a : K) - c) hn) : K) = rv O (g e p : K) :=
        (hP e _).symm.trans ((congrArg (P e) hrv).trans (hP e p))
      have hEq : rv O y = rv O (d * (g e p : K)) := by
        rw [he, map_mul (rv O), hpow, ← map_mul (rv O)]
      exact (hy ⟨d * (g e p : K), A.mul_mem hd (hbase e p hp),
        by simpa only [unsignedValue_rv] using congrArg (unsignedValue O) hEq.symm⟩).elim
  by_cases hx1 : O.valuation x = 1
  · have hv : O.valuation ((a : K) * x) ≠ 1 := by
      rw [map_mul, hx1, mul_one]
      exact ha.ne
    obtain ⟨d, hd, e, he⟩ :=
      hnew ((a : K) * x) (B.mul_mem haB hxB) (mul_ne_zero a.property.ne' hx0) hv
    have hpow : (g (e - 1) a : K) * a = g e a := by
      have h : g (e - 1) a * a = g e a := calc
        g (e - 1) a * a = g (e - 1) a * g 1 a := congrArg (g (e - 1) a * ·) hone.symm
        _ = g ((e - 1) + 1) a := (hadd _ _).symm
        _ = g e a := by rw [sub_add_cancel]
      exact congrArg Subtype.val h
    have hEq : rv O a * rv O x = rv O a * (rv O d * rv O (g (e - 1) a : K)) := calc
      _ = rv O ((a : K) * x) := (map_mul (rv O) (a : K) x).symm
      _ = rv O d * rv O (g e a : K) := he
      _ = rv O d * (rv O (g (e - 1) a : K) * rv O a) := by
        rw [← map_mul (rv O) (g (e - 1) a : K) (a : K), hpow]
      _ = (rv O d * rv O (g (e - 1) a : K)) * rv O a :=
        (mul_assoc (rv O d) (rv O (g (e - 1) a : K)) (rv O a)).symm
      _ = _ := mul_comm (rv O d * rv O (g (e - 1) a : K)) (rv O a)
    have hane : rv O a ≠ 0 := (rv_eq_zero_iff O).not.mpr a.property.ne'
    exact ⟨d, hd, e - 1, by rw [hP]; exact rv_mul_left_cancel O hane hEq⟩
  · obtain ⟨d, hd, e, he⟩ := hnew x hxB hx0 hx1
    exact ⟨d, hd, e, by rw [hP]; exact he⟩

/-- The monomial description also applies when the prescribed positive
representative has value above one. Inverting it changes the exponent
sign and leaves the generated field unchanged. -/
theorem trivialBase_leadingTerm_of_value_ne_one [Ring E]
    {g : E → PositiveField K →* PositiveField K} {P : E → RV0 O → RV0 O}
    {A B : Subfield K} (hO : IsOrderConvex O) (a : PositiveField K)
    (haB : (a : K) ∈ B) (ha : O.valuation (a : K) ≠ 1)
    (htriv : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1)
    (hbase : ∀ e (x : PositiveField K), (x : K) ∈ A → (g e x : K) ∈ A)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
    (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
    (hFreni : LeadingTermMonomialTransfer O g A B a)
    (hFreniInv : LeadingTermMonomialTransfer O g A B ((a⁻¹ : PositiveField K) : K))
    {x : K} (hxB : x ∈ B) (hx0 : x ≠ 0) :
    ∃ d ∈ A, ∃ e : E, rv O x = rv O d * P e (rv O a) := by
  rcases lt_or_gt_of_ne ha with h | h
  · exact trivialBase_leadingTerm O hO a haB h htriv hbase hP (hone a)
      (fun e d => hadd e d a) hFreni hxB hx0
  · have hB : ((a⁻¹ : PositiveField K) : K) ∈ B := by
      rw [Positive.coe_inv]
      exact B.inv_mem haB
    have hl : O.valuation ((a⁻¹ : PositiveField K) : K) < 1 := by
      rw [Positive.coe_inv, map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
    obtain ⟨d, hd, e, he⟩ := trivialBase_leadingTerm O hO a⁻¹ hB hl htriv hbase hP
      (hone a⁻¹) (fun e d => hadd e d a⁻¹) hFreniInv hxB hx0
    have hneg : g (-e) a = (g e a)⁻¹ := by
      calc
        g (-e) a = (g (-e) a * g e a) * (g e a)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = (g e a)⁻¹ := by rw [← hadd, neg_add_cancel, hzero, one_mul]
    have hpow : P e (rv O ((a⁻¹ : PositiveField K) : K)) = P (-e) (rv O a) := by
      rw [hP e a⁻¹, hP (-e) a, map_inv, hneg]
    exact ⟨d, hd, -e, hpow ▸ he⟩

omit [IsStrictOrderedRing K] in
/-- A new residue over a trivially valued base leaves the generated
field trivially valued, by the valuation property of Proposition 2.21. -/
theorem trivialBase_values_eq_of_new_residue {A B : Subfield K} {a : K}
    (ha : O.valuation a = 1) (hnew : rv O a ∉ fieldRV O A)
    (htriv : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1)
    (hValProp : ∀ y ∈ B, O.valuation y ∉ O.valuation '' (A : Set K) →
      ∃ c ∈ A, O.valuation (a - c) ∉ O.valuation '' (A : Set K)) :
    ∀ y ∈ B, y ≠ 0 → O.valuation y = 1 := by
  have translates (c : K) (hc : c ∈ A) : O.valuation (a - c) = 1 := by
    by_cases hc0 : c = 0
    · simpa only [hc0, sub_zero] using ha
    have hc1 := htriv c hc hc0
    have hle := O.valuation.map_sub a c
    rw [ha, hc1, max_self] at hle
    refine le_antisymm hle (not_lt.mp ?_)
    intro hlt
    have hr : rv O a = rv O c :=
      (rv_eq_rv_iff_valuation O hc0).mpr (hc1.symm ▸ hlt)
    exact hnew ⟨c, hc, hr.symm⟩
  intro y hy hny
  by_contra h
  have hyNew : O.valuation y ∉ O.valuation '' (A : Set K) := by
    rintro ⟨c, hc, hcval⟩
    by_cases hc0 : c = 0
    · rw [hc0, map_zero] at hcval
      exact ((map_ne_zero O.valuation).mpr hny) hcval.symm
    · exact h (hcval.symm.trans (htriv c hc hc0))
  obtain ⟨c, hc, hcut⟩ := hValProp y hy hyNew
  exact hcut ⟨1, A.one_mem, (map_one O.valuation).trans (translates c hc).symm⟩

end GeneralizedEuler.Section2
