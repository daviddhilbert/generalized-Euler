module

public import Section2.Residue

/-! The order of the residue field of a convex valuation ring. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

private theorem residueQuotient_fiber_ordConnected (hO : IsOrderConvex O)
    (q : Quotient (Setoid.ker (IsLocalRing.residue O))) :
    Set.OrdConnected (Quotient.mk _ ⁻¹' {q}) := by
  induction q using Quotient.inductionOn with
  | h y =>
    have heq : Quotient.mk (Setoid.ker (IsLocalRing.residue O)) ⁻¹' {⟦y⟧} =
        Subtype.val ⁻¹' {x : K | O.valuation (x - (y : K)) < 1} := by
      ext x
      exact Quotient.eq.trans (residue_eq_iff_valuation_sub_lt_one O x y)
    rw [heq]
    exact (valuativeDisc_ordConnected O hO (y : K) (Set.Iio 1)
      (fun {_ _} hab hb => lt_of_le_of_lt hab hb)).preimage_mono
        (fun _ _ h => h)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private abbrev residueQuotientEquiv :
    Quotient (Setoid.ker (IsLocalRing.residue O)) ≃ Residue O :=
  Setoid.quotientKerEquivOfSurjective (IsLocalRing.residue O) IsLocalRing.residue_surjective

/-- The order on the residue field given by the convex reduction fibers. -/
@[instance_reducible]
def residueLinearOrder (hO : IsOrderConvex O) : LinearOrder (Residue O) := by
  classical
  letI := residueQuotient_fiber_ordConnected O hO
  exact LinearOrder.lift' (residueQuotientEquiv O).symm (residueQuotientEquiv O).symm.injective

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem residueQuotientEquiv_symm_residue (x : O) :
    (residueQuotientEquiv O).symm (IsLocalRing.residue O x) = ⟦x⟧ :=
  (residueQuotientEquiv O).symm_apply_eq.mpr rfl

theorem residue_le_residue_iff (hO : IsOrderConvex O) {x y : O} :
    letI := residueLinearOrder O hO
    IsLocalRing.residue O x ≤ IsLocalRing.residue O y ↔
      x ≤ y ∨ IsLocalRing.residue O x = IsLocalRing.residue O y := by
  classical
  change (residueQuotientEquiv O).symm (IsLocalRing.residue O x) ≤
    (residueQuotientEquiv O).symm (IsLocalRing.residue O y) ↔ _
  rw [residueQuotientEquiv_symm_residue, residueQuotientEquiv_symm_residue]
  exact @Quotient.mk_le_mk _ _ _ (residueQuotient_fiber_ordConnected O hO) _ _

theorem residue_lt_residue_iff (hO : IsOrderConvex O) {x y : O} :
    letI := residueLinearOrder O hO
    IsLocalRing.residue O x < IsLocalRing.residue O y ↔
      x < y ∧ IsLocalRing.residue O x ≠ IsLocalRing.residue O y := by
  classical
  change (residueQuotientEquiv O).symm (IsLocalRing.residue O x) <
    (residueQuotientEquiv O).symm (IsLocalRing.residue O y) ↔ _
  rw [residueQuotientEquiv_symm_residue, residueQuotientEquiv_symm_residue]
  exact @Quotient.mk_lt_mk _ _ _ (residueQuotient_fiber_ordConnected O hO) _ _

theorem residue_monotone (hO : IsOrderConvex O) :
    letI := residueLinearOrder O hO
    Monotone (IsLocalRing.residue O) :=
  fun _ _ h => (residue_le_residue_iff O hO).mpr (Or.inl h)

/-- A positive residue has a positive representative in the valuation ring. -/
theorem exists_positive_residue_representative (hO : IsOrderConvex O) {r : Residue O}
    (hr : letI := residueLinearOrder O hO; 0 < r) :
    ∃ y : O, 0 < (y : K) ∧ IsLocalRing.residue O y = r := by
  obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective r
  have h : letI := residueLinearOrder O hO
           IsLocalRing.residue O 0 < IsLocalRing.residue O y := by
    rw [map_zero, hy]
    exact hr
  exact ⟨y, ((residue_lt_residue_iff O hO).mp h).1, hy⟩

set_option linter.style.haveILetI false in
private theorem residue_mul_mono (hO : IsOrderConvex O) {a b c : Residue O} :
    letI := residueLinearOrder O hO
    0 ≤ a → b ≤ c → a * b ≤ a * c := by
  letI := residueLinearOrder O hO
  intro ha hbc
  obtain ha0 | ha := ha.eq_or_lt
  · subst a
    rw [zero_mul, zero_mul]
  obtain ⟨x, hx0, hx⟩ := exists_positive_residue_representative O hO ha
  obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective b
  obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective c
  rw [← hy, ← hz] at hbc
  rw [← hx, ← hy, ← hz]
  rw [← map_mul, ← map_mul]
  rcases (residue_le_residue_iff O hO).mp hbc with h | h
  · exact residue_monotone O hO (show x * y ≤ x * z from
      mul_le_mul_of_nonneg_left (α := K) h hx0.le)
  · simp only [map_mul, h, le_refl]

set_option linter.style.haveILetI false in
/-- The quotient order and the residue-field operations form an ordered field. -/
theorem residue_isOrderedRing (hO : IsOrderConvex O) :
    letI := residueLinearOrder O hO
    IsOrderedRing (Residue O) := by
  letI := residueLinearOrder O hO
  refine
    { zero_le_one := ?_
      add_le_add_left := ?_
      mul_le_mul_of_nonneg_left := fun _ ha _ _ hbc => residue_mul_mono O hO ha hbc
      mul_le_mul_of_nonneg_right := fun _ ha _ _ hbc => by
        simpa only [mul_comm] using residue_mul_mono O hO ha hbc }
  · intro a b hab c
    obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective a
    obtain ⟨y, hy⟩ := IsLocalRing.residue_surjective b
    obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective c
    rw [← hx, ← hy] at hab
    rw [← hx, ← hy, ← hz]
    rcases (residue_le_residue_iff O hO).mp hab with h | h
    · rw [← map_add, ← map_add]
      exact residue_monotone O hO (show x + z ≤ y + z from (add_le_add_left (α := K) h z))
    · rw [h]
  · have h : (0 : O) ≤ 1 := (zero_le_one : (0 : K) ≤ 1)
    simpa only [map_zero, map_one] using residue_monotone O hO h

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem exists_residueRV_representative (r : Residue O) :
    ∃ x : O, IsLocalRing.residue O x = r ∧ rv O (x : K) = residueRV O r := by
  by_cases hr : r = 0
  · subst r
    exact ⟨0, map_zero _, by
      rw [residueRV_zero]
      exact map_zero (rv O)⟩
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective r
  exact ⟨x, hx, (residueRV_residue_of_ne_zero O x (hx.trans_ne hr)).symm.trans
    (congrArg (residueRV O) hx)⟩

/-- The embedded residue field has its quotient-field order as a subset of RV₀. -/
theorem residueRV_strictMono (hO : IsOrderConvex O) :
    letI := rvLinearOrder O hO
    letI := residueLinearOrder O hO
    StrictMono (residueRV O) := by
  intro r s hrs
  obtain ⟨x, hx, hxr⟩ := exists_residueRV_representative O r
  obtain ⟨y, hy, hyr⟩ := exists_residueRV_representative O s
  rw [← hxr, ← hyr]
  rw [← hx, ← hy] at hrs
  exact (rv_lt_rv_iff O hO).mpr
    ⟨((residue_lt_residue_iff O hO).mp hrs).1, fun heq =>
      ((residue_lt_residue_iff O hO).mp hrs).2
        (hx.trans ((residueRV_injective O (hxr.symm.trans (heq.trans hyr))).trans hy.symm))⟩

end GeneralizedEuler.Section2
