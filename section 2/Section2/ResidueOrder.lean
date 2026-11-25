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
