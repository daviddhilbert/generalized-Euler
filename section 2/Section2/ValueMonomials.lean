module

public import Section2.RVVectorSpace
public import Section2.PrescribedLift

/-! The leading-term calculation in the new-value branch of Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {E : Type*} [Field E] (O : ValuationSubring K)
  (g : E → PositiveField K →* PositiveField K)
  (P : E → RV0 O → RV0 O) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

set_option linter.style.haveILetI false in
/-- Relative value rank at most one and unchanged residues give the
monomial representation over the old field. The residue coefficient
is absorbed into the old field factor. -/
theorem exists_rv_monomial_of_relative_rank (A : Subfield K) (a : PositiveField K) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    ∀ (U : Submodule E (Additive (O.ValueGroupˣ))) [FiniteDimensional E (_ ⧸ U)],
      Module.finrank E (_ ⧸ U) ≤ 1 → positiveFieldValue O a ∉ U →
      (∀ z ∈ U, ∃ c : PositiveField K, c.val ∈ A ∧ positiveFieldValue O c = z) →
      (∀ x : K, O.valuation x = 1 → rv O x ∈ rv O '' (A : Set K)) →
      ∀ x : K, x ≠ 0 → ∃ d ∈ A, ∃ e : E, rv O x = rv O d * P e (rv O a.val) := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  intro U _ hd ha hbase hresidue x hx
  have hspan := span_base_and_new_value_of_relative_finrank_le_one U hd ha
  let p : PositiveField K := ⟨|x|, abs_pos.mpr hx⟩
  have hp : positiveFieldValue O p ∈ U ⊔ Submodule.span E {positiveFieldValue O a} :=
    hspan ▸ Submodule.mem_top
  obtain ⟨z, hz, q, hq, hsum⟩ := Submodule.mem_sup.mp hp
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hq
  obtain ⟨c, hc, hcv⟩ := hbase z hz
  have hmulValue : positiveFieldValue O p = positiveFieldValue O c + positiveFieldValue O (g e a) := by
    rw [hcv, positiveFieldValue_power O g P hP hzero hone hadd hmul hunit]
    exact hsum.symm
  have hval := congrArg (fun t : Additive (O.ValueGroupˣ) => (t.toMul : O.ValueGroup)) hmulValue
  change ((positiveFieldValue O p).toMul : O.ValueGroup) =
    ((positiveFieldValue O c).toMul : O.ValueGroup) * ((positiveFieldValue O (g e a)).toMul : O.ValueGroup) at hval
  rw [positiveFieldValue_coe, positiveFieldValue_coe, positiveFieldValue_coe] at hval
  change O.valuation |x| = O.valuation (c : K) * O.valuation (g e a : K) at hval
  rw [valuation_abs, ← map_mul] at hval
  have hne : (c : K) * (g e a : K) ≠ 0 := mul_ne_zero c.property.ne' (g e a).property.ne'
  have hquot : O.valuation (x / ((c : K) * (g e a : K))) = 1 := by
    rw [map_div₀, hval, div_self ((map_ne_zero O.valuation).mpr hne)]
  obtain ⟨d, hd, hrv⟩ := rv_absorb_coefficient O hc hne (hresidue _ hquot)
  exact ⟨d, hd, e, hrv.trans (congrArg (fun z : RV0 O => rv O d * z) (hP e a).symm)⟩

end GeneralizedEuler.Section2
