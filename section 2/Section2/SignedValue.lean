module

public import Section2.LeadingTermOrder
public import Mathlib.Basic.Sign.Basic

/-! The signed value group in §2.2 and its unsigned quotient. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open SignType

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

/-- The nonzero signed values retain the sign together with the unsigned
value. Zero is adjoined separately. -/
abbrev SignedValueGroup := SignTypeˣ × O.ValueGroupˣ

private def signedValueOnFieldUnits : Kˣ →* SignedValueGroup O :=
  (Units.map (signHom (α := K)).toMonoidHom).prod (Units.map O.valuation.toMonoidHom)

/-- The signed value of a nonzero leading-term class. -/
def signedValueUnit (hO : IsOrderConvex O) : RV O →* SignedValueGroup O :=
  QuotientGroup.lift O.principalUnitGroup (signedValueOnFieldUnits O) (by
    intro x hx
    apply Prod.ext <;> apply Units.ext
    · change sign (x : K) = 1
      exact sign_eq_one_iff.mpr ((by positivity : (0 : K) < 1 / 2).trans (principalUnit_bounds O hO hx).1)
    · exact (O.mem_unitGroup_iff x).mp (O.principal_units_le_units hx))

/-- The signed value map on RV, with value zero at the middle element. -/
def signedValue (hO : IsOrderConvex O) : RV0 O →*₀ WithZero (SignedValueGroup O) :=
  WithZero.map' (signedValueUnit O hO)

private theorem signedValueUnit_rvUnit (hO : IsOrderConvex O) (x : Kˣ) :
    signedValueUnit O hO (rvUnit O x) = signedValueOnFieldUnits O x := by
  rfl

theorem signedValue_rv_of_ne_zero (hO : IsOrderConvex O) {x : K} (hx : x ≠ 0) :
    signedValue O hO (rv O x) =
      (⟨Units.mk0 (sign x) (sign_eq_zero_iff.not.mpr hx),
        Units.mk0 (O.valuation x) ((map_ne_zero O.valuation).mpr hx)⟩ : SignedValueGroup O) := by
  let u := Units.mk0 x hx
  change signedValue O hO (rv O (u : K)) = _
  rw [rv_coe_unit, signedValue, WithZero.map'_coe, signedValueUnit_rvUnit, WithZero.coe_inj]
  exact Prod.ext (Units.ext rfl) (Units.ext rfl)

set_option linter.style.haveILetI false in
/-- The kernel consists of the positive classes of unsigned value one,
which are precisely the positive residue classes. -/
theorem signedValueUnit_eq_one_iff (hO : IsOrderConvex O) (t : RV O) :
    signedValueUnit O hO t = 1 ↔
      letI := rvLinearOrder O hO
      0 < (t : RV0 O) ∧ unsignedValue O (t : RV0 O) = 1 := by
  letI := rvLinearOrder O hO
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O.principalUnitGroup t
  rw [signedValueUnit_rvUnit, ← rv_coe_unit, zero_lt_rv_iff O hO, unsignedValue_rv]
  change (Units.map (signHom (α := K)).toMonoidHom x,
    Units.map O.valuation.toMonoidHom x) = (1, 1) ↔
      0 < (x : K) ∧ O.valuation x = 1
  rw [Prod.mk.injEq, ← Units.val_inj, ← Units.val_inj]
  exact and_congr sign_eq_one_iff Iff.rfl

theorem signedValueUnit_surjective (hO : IsOrderConvex O) :
    Function.Surjective (signedValueUnit O hO) := by
  rintro ⟨s, γ⟩
  obtain ⟨x, hx⟩ := O.valuation_surjective (γ : O.ValueGroup)
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hx
    exact γ.ne_zero hx.symm
  have hs : (s : SignType) = 1 ∨ (s : SignType) = -1 := by
    rcases he : (s : SignType) with _ | _ | _
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact (s.ne_zero he).elim
  rcases hs with hpos | hneg
  · let u := Units.mk0 |x| (abs_ne_zero.mpr hx0)
    refine ⟨rvUnit O u, ?_⟩
    rw [signedValueUnit_rvUnit]
    apply Prod.ext <;> apply Units.ext
    · change sign |x| = (s : SignType)
      rw [hpos]
      exact sign_eq_one_iff.mpr (abs_pos.mpr hx0)
    · change O.valuation |x| = (γ : O.ValueGroup)
      rwa [valuation_abs]
  · let u := Units.mk0 (-|x|) (neg_ne_zero.mpr (abs_ne_zero.mpr hx0))
    refine ⟨rvUnit O u, ?_⟩
    rw [signedValueUnit_rvUnit]
    apply Prod.ext <;> apply Units.ext
    · change sign (-|x|) = (s : SignType)
      rw [hneg]
      exact sign_eq_neg_one_iff.mpr (neg_lt_zero.mpr (abs_pos.mpr hx0))
    · change O.valuation (-|x|) = (γ : O.ValueGroup)
      rwa [O.valuation.map_neg, valuation_abs]

/-- An explicit realization of the quotient of RV by the kernel of the
signed valuation. -/
def signedValueQuotientEquiv (hO : IsOrderConvex O) :
    RV O ⧸ (signedValueUnit O hO).ker ≃* SignedValueGroup O :=
  QuotientGroup.quotientKerEquivOfSurjective (signedValueUnit O hO) (signedValueUnit_surjective O hO)

/-- Forgetting the sign gives the unsigned value group. -/
def signedToUnsignedValue : SignedValueGroup O →* O.ValueGroupˣ :=
  MonoidHom.snd _ _

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem signedToUnsignedValue_eq_one_iff (p : SignedValueGroup O) :
    signedToUnsignedValue O p = 1 ↔ p.2 = 1 := Iff.rfl

/-- The quotient by the two unit signs is the unsigned value group. -/
def unsignedValueQuotientEquiv :
    SignedValueGroup O ⧸ (signedToUnsignedValue O).ker ≃* O.ValueGroupˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (signedToUnsignedValue O)
    (fun γ => ⟨(1, γ), rfl⟩)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Forgetting the sign also preserves the separate zero value. -/
def signedToUnsignedWithZero : WithZero (SignedValueGroup O) →*₀ O.ValueGroup :=
  WithZero.lift' ((Units.coeHom O.ValueGroup).comp (signedToUnsignedValue O))

theorem signedToUnsigned_signedValue (hO : IsOrderConvex O) (t : RV0 O) :
    signedToUnsignedWithZero O (signedValue O hO t) = unsignedValue O t := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  by_cases hx : x = 0
  · simp [hx]
  rw [signedValue_rv_of_ne_zero O hO hx, unsignedValue_rv]
  rfl

/-- The signed valuation is the composite of leading term and signed value. -/
def signedValuation (hO : IsOrderConvex O) : K →*₀ WithZero (SignedValueGroup O) :=
  (signedValue O hO).comp (rv O)

theorem signedValuation_eq_iff (hO : IsOrderConvex O) (x y : K) :
    signedValuation O hO x = signedValuation O hO y ↔
      sign x = sign y ∧ O.valuation x = O.valuation y := by
  change signedValue O hO (rv O x) = signedValue O hO (rv O y) ↔ _
  by_cases hx : x = 0
  · subst x
    by_cases hy : y = 0
    · simp [hy]
    rw [map_zero, map_zero, signedValue_rv_of_ne_zero O hO hy, sign_zero, map_zero]
    refine ⟨fun h => (WithZero.coe_ne_zero h.symm).elim, fun h => ?_⟩
    exact ((map_ne_zero O.valuation).mpr hy h.2.symm).elim
  by_cases hy : y = 0
  · subst y
    rw [map_zero, map_zero, signedValue_rv_of_ne_zero O hO hx, sign_zero, map_zero]
    refine ⟨fun h => (WithZero.coe_ne_zero h).elim, fun h => ?_⟩
    exact ((map_ne_zero O.valuation).mpr hx h.2).elim
  rw [signedValue_rv_of_ne_zero O hO hx, signedValue_rv_of_ne_zero O hO hy, WithZero.coe_inj,
    Prod.mk.injEq, ← Units.val_inj, ← Units.val_inj]
  rfl

set_option linter.style.haveILetI false in
/-- The signed value equivalence is detected by unsigned value and the
negative branch test in RV. -/
theorem signedValue_eq_iff (hO : IsOrderConvex O) (s t : RV0 O) :
    letI := rvLinearOrder O hO
    signedValue O hO s = signedValue O hO t ↔
      unsignedValue O s = unsignedValue O t ∧ (s < 0 ↔ t < 0) := by
  letI := rvLinearOrder O hO
  obtain ⟨x, rfl⟩ := rv_surjective O s
  obtain ⟨y, rfl⟩ := rv_surjective O t
  change signedValuation O hO x = signedValuation O hO y ↔ _
  rw [signedValuation_eq_iff, unsignedValue_rv, unsignedValue_rv,
    rv_lt_zero_iff O hO, rv_lt_zero_iff O hO]
  constructor
  · rintro ⟨h, v⟩
    exact ⟨v, by rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h]⟩
  · rintro ⟨v, hs⟩
    refine ⟨?_, v⟩
    by_cases hx : x = 0
    · have hy : y = 0 := (map_eq_zero O.valuation).mp (v.symm.trans (hx ▸ map_zero O.valuation))
      rw [hx, hy]
    by_cases hn : x < 0
    · rw [sign_eq_neg_one_iff.mpr hn, sign_eq_neg_one_iff.mpr (hs.mp hn)]
    have hy : y ≠ 0 := fun h => hx ((map_eq_zero O.valuation).mp (v.trans (h ▸ map_zero O.valuation)))
    have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (fun h => hx h.symm)
    have hq : 0 < y := lt_of_le_of_ne (le_of_not_gt (fun h => hn (hs.mpr h))) hy.symm
    rw [sign_eq_one_iff.mpr hp, sign_eq_one_iff.mpr hq]

theorem signedValuation_fiber_ordConnected (hO : IsOrderConvex O)
    (t : WithZero (SignedValueGroup O)) : Set.OrdConnected (signedValuation O hO ⁻¹' {t}) := by
  constructor
  intro a ha c hc b hb
  have hac : signedValuation O hO a = signedValuation O hO c := ha.trans hc.symm
  obtain ⟨hs, hv⟩ := (signedValuation_eq_iff O hO a c).mp hac
  suffices h : sign b = sign a ∧ O.valuation b = O.valuation a from
    ((signedValuation_eq_iff O hO b a).mpr h).trans ha
  rcases lt_trichotomy a 0 with hn | rfl | hp
  · have hc' : c < 0 := sign_eq_neg_one_iff.mp (hs.symm.trans (sign_eq_neg_one_iff.mpr hn))
    have hb' : b < 0 := hb.2.trans_lt hc'
    have h₁ := valuation_le_of_nonneg_le O hO (neg_nonneg.mpr hb'.le) (neg_le_neg hb.1)
    have h₂ := valuation_le_of_nonneg_le O hO (neg_nonneg.mpr hc'.le) (neg_le_neg hb.2)
    rw [O.valuation.map_neg, O.valuation.map_neg] at h₁ h₂
    exact ⟨(sign_eq_neg_one_iff.mpr hb').trans (sign_eq_neg_one_iff.mpr hn).symm,
      h₁.antisymm (hv.symm ▸ h₂)⟩
  · have hc' : c = 0 := sign_eq_zero_iff.mp (hs.symm.trans sign_zero)
    have hb' : b = 0 := le_antisymm (hc' ▸ hb.2) hb.1
    simp [hb']
  · have hb' : 0 < b := hp.trans_le hb.1
    have h₁ := valuation_le_of_nonneg_le O hO hp.le hb.1
    have h₂ := valuation_le_of_nonneg_le O hO hb'.le hb.2
    exact ⟨(sign_eq_one_iff.mpr hb').trans (sign_eq_one_iff.mpr hp).symm,
      (h₂.trans_eq hv.symm).antisymm h₁⟩

private theorem signedValuation_surjective (hO : IsOrderConvex O) :
    Function.Surjective (signedValuation O hO) :=
  (WithZero.map'_surjective (signedValueUnit_surjective O hO)).comp (rv_surjective O)

private theorem signedValuationQuotient_fiber_ordConnected (hO : IsOrderConvex O)
    (q : Quotient (Setoid.ker (signedValuation O hO))) :
    Set.OrdConnected (Quotient.mk _ ⁻¹' {q}) := by
  induction q using Quotient.inductionOn with
  | h y =>
    have he : Quotient.mk (Setoid.ker (signedValuation O hO)) ⁻¹' {⟦y⟧} =
        signedValuation O hO ⁻¹' {signedValuation O hO y} := by
      ext x
      exact Quotient.eq
    rw [he]
    exact signedValuation_fiber_ordConnected O hO _

private abbrev signedValuationQuotientEquiv (hO : IsOrderConvex O) :
    Quotient (Setoid.ker (signedValuation O hO)) ≃ WithZero (SignedValueGroup O) :=
  Setoid.quotientKerEquivOfSurjective (signedValuation O hO) (signedValuation_surjective O hO)

/-- The order induced by the field order on the signed values. The
zero class lies between the negative and positive branches. -/
@[instance_reducible]
def signedValueLinearOrder (hO : IsOrderConvex O) : LinearOrder (WithZero (SignedValueGroup O)) := by
  classical
  letI := signedValuationQuotient_fiber_ordConnected O hO
  exact LinearOrder.lift' (signedValuationQuotientEquiv O hO).symm
    (signedValuationQuotientEquiv O hO).symm.injective

theorem signedValuation_lt_iff (hO : IsOrderConvex O) (x y : K) :
    (signedValueLinearOrder O hO).lt (signedValuation O hO x) (signedValuation O hO y) ↔
      x < y ∧ signedValuation O hO x ≠ signedValuation O hO y := by
  classical
  let h := signedValuationQuotient_fiber_ordConnected O hO
  let e := signedValuationQuotientEquiv O hO
  have he (a : K) : e.symm (signedValuation O hO a) = ⟦a⟧ :=
    e.symm_apply_eq.mpr rfl
  change e.symm (signedValuation O hO x) < e.symm (signedValuation O hO y) ↔ _
  rw [he, he]
  exact @Quotient.mk_lt_mk _ _ _ h _ _

set_option linter.style.haveILetI false in
/-- Order of different signed values is read from their leading terms. -/
theorem signedValue_lt_iff (hO : IsOrderConvex O) (s t : RV0 O) :
    letI := rvLinearOrder O hO
    (signedValueLinearOrder O hO).lt (signedValue O hO s) (signedValue O hO t) ↔
      s ≤ t ∧ signedValue O hO s ≠ signedValue O hO t := by
  letI := rvLinearOrder O hO
  obtain ⟨x, rfl⟩ := rv_surjective O s
  obtain ⟨y, rfl⟩ := rv_surjective O t
  change (signedValueLinearOrder O hO).lt (signedValuation O hO x) (signedValuation O hO y) ↔ _
  rw [signedValuation_lt_iff, rv_le_rv_iff O hO]
  constructor
  · exact fun h => ⟨Or.inl h.1.le, h.2⟩
  · rintro ⟨h | h, hn⟩
    · exact ⟨lt_of_le_of_ne h (fun he => hn (he ▸ rfl)), hn⟩
    · exact (hn (congrArg (signedValue O hO) h)).elim

end GeneralizedEuler.Section2
