module

public import Mathlib.Order.Quotient
public import Mathlib.Order.Setoid.Basic
public import Section2.ConvexValuation

/-! The signed RV order of Ax. 3, obtained by ordering the convex fibers of
the leading-term map. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

theorem valuation_le_of_nonneg_le (hO : IsOrderConvex O) {x y : K}
    (hx : 0 ≤ x) (hxy : x ≤ y) : O.valuation x ≤ O.valuation y := by
  rcases (hx.trans hxy).eq_or_lt with hy | hy
  · have hx0 : x = 0 := hx.antisymm' (hxy.trans hy.ge)
    simp [hx0]
  · have hdiv : x / y ∈ O := hO.out (O.zero_mem) (O.one_mem)
      ⟨div_nonneg hx hy.le, (div_le_one₀ hy).mpr hxy⟩
    exact (O.valuation_le_iff x y).mpr
      ⟨⟨x / y, hdiv⟩, div_mul_cancel₀ x hy.ne'⟩

theorem valuation_abs (a : K) : O.valuation |a| = O.valuation a := by
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg ha, O.valuation.map_neg]

theorem valuation_le_of_abs_le_abs (hO : IsOrderConvex O) {x y : K}
    (hxy : |x| ≤ |y|) : O.valuation x ≤ O.valuation y := by
  simpa only [valuation_abs] using valuation_le_of_nonneg_le O hO (abs_nonneg x) hxy

/-- Every closed or open valuative disc is order-convex. This comparison
works with both choices of the threshold relation. -/
theorem valuativeDisc_ordConnected (hO : IsOrderConvex O)
    (center : K) (S : Set O.ValueGroup) (hS : ∀ ⦃a b⦄, a ≤ b → b ∈ S → a ∈ S) :
    Set.OrdConnected {x | O.valuation (x - center) ∈ S} := by
  refine ⟨?_⟩
  intro x hx y hy z ⟨hxz, hzy⟩
  rcases le_or_gt center z with hz | hz
  · have hzy' : |z - center| ≤ |y - center| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hz), abs_of_nonneg (sub_nonneg.mpr (hz.trans hzy))]
      exact sub_le_sub_right hzy center
    exact hS (valuation_le_of_abs_le_abs O hO hzy') hy
  · have hzx' : |z - center| ≤ |x - center| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hz.le),
        abs_of_nonpos (sub_nonpos.mpr (hxz.trans hz.le))]
      exact neg_le_neg (sub_le_sub_right hxz center)
    exact hS (valuation_le_of_abs_le_abs O hO hzx') hx

theorem rv_fiber_ordConnected (hO : IsOrderConvex O) (t : RV0 O) :
    Set.OrdConnected (rv O ⁻¹' {t}) := by
  obtain ⟨y, rfl⟩ := rv_surjective O t
  by_cases hy : y = 0
  · subst y
    simpa only [map_zero, Set.preimage, Set.mem_singleton_iff, rv_eq_zero_iff,
      Set.ofPred_eq_eq_singleton] using (Set.ordConnected_singleton (a := (0 : K)))
  have hset : rv O ⁻¹' {rv O y} = {x | O.valuation (x - y) < O.valuation y} := by
    ext x
    exact rv_eq_rv_iff_valuation O hy
  rw [hset]
  exact valuativeDisc_ordConnected O hO y (Set.Iio (O.valuation y))
    (fun {_ _} hab hb => lt_of_le_of_lt hab hb)

private theorem rvQuotient_fiber_ordConnected (hO : IsOrderConvex O)
    (q : Quotient (Setoid.ker (rv O))) :
    Set.OrdConnected (Quotient.mk _ ⁻¹' {q}) := by
  induction q using Quotient.inductionOn with
  | h y =>
    have hset : Quotient.mk (Setoid.ker (rv O)) ⁻¹' {⟦y⟧} = rv O ⁻¹' {rv O y} := by
      ext x
      exact Quotient.eq
    rw [hset]
    exact rv_fiber_ordConnected O hO _

private abbrev rvQuotientEquiv : Quotient (Setoid.ker (rv O)) ≃ RV0 O :=
  Setoid.quotientKerEquivOfSurjective (rv O) (rv_surjective O)

/-- The ordering on RV₀ induced by the field order. The zero class lies
between the classes of negative and positive field elements. -/
@[instance_reducible]
def rvLinearOrder (hO : IsOrderConvex O) : LinearOrder (RV0 O) := by
  classical
  letI := rvQuotient_fiber_ordConnected O hO
  exact LinearOrder.lift' (rvQuotientEquiv O).symm (rvQuotientEquiv O).symm.injective

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rvQuotientEquiv_symm_rv (x : K) :
    (rvQuotientEquiv O).symm (rv O x) = ⟦x⟧ :=
  (rvQuotientEquiv O).symm_apply_eq.mpr rfl

theorem rv_le_rv_iff (hO : IsOrderConvex O) {x y : K} :
    letI := rvLinearOrder O hO
    rv O x ≤ rv O y ↔ x ≤ y ∨ rv O x = rv O y := by
  classical
  let h := rvQuotient_fiber_ordConnected O hO
  change (rvQuotientEquiv O).symm (rv O x) ≤ (rvQuotientEquiv O).symm (rv O y) ↔ _
  rw [rvQuotientEquiv_symm_rv, rvQuotientEquiv_symm_rv]
  exact @Quotient.mk_le_mk _ _ _ h _ _

theorem rv_lt_rv_iff (hO : IsOrderConvex O) {x y : K} :
    letI := rvLinearOrder O hO
    rv O x < rv O y ↔ x < y ∧ rv O x ≠ rv O y := by
  classical
  let h := rvQuotient_fiber_ordConnected O hO
  change (rvQuotientEquiv O).symm (rv O x) < (rvQuotientEquiv O).symm (rv O y) ↔ _
  rw [rvQuotientEquiv_symm_rv, rvQuotientEquiv_symm_rv]
  exact @Quotient.mk_lt_mk _ _ _ h _ _

/-- The strict quotient order is equivalent to comparing every pair of
representatives of the two fibers. -/
theorem rv_lt_iff_all_representatives (hO : IsOrderConvex O) {s t : RV0 O} :
    letI := rvLinearOrder O hO
    s < t ↔ ∀ x y : K, rv O x = s → rv O y = t → x < y := by
  constructor
  · intro h x y hx hy
    exact ((rv_lt_rv_iff O hO).mp (hx ▸ hy ▸ h)).1
  · intro h
    obtain ⟨x, rfl⟩ := rv_surjective O s
    obtain ⟨y, rfl⟩ := rv_surjective O t
    exact (rv_lt_rv_iff O hO).mpr
      ⟨h x y rfl rfl, fun heq => (lt_irrefl x) (h x x rfl heq)⟩

@[simp] theorem rv_lt_zero_iff (hO : IsOrderConvex O) {x : K} :
    letI := rvLinearOrder O hO
    rv O x < 0 ↔ x < 0 := by
  rw [← map_zero (rv O), rv_lt_rv_iff O hO, map_zero, ne_eq, rv_eq_zero_iff]
  exact ⟨And.left, fun h => ⟨h, h.ne⟩⟩

@[simp] theorem zero_lt_rv_iff (hO : IsOrderConvex O) {x : K} :
    letI := rvLinearOrder O hO
    0 < rv O x ↔ 0 < x := by
  rw [← map_zero (rv O), rv_lt_rv_iff O hO, map_zero, ne_eq, eq_comm, rv_eq_zero_iff]
  exact ⟨And.left, fun h => ⟨h, h.ne'⟩⟩

/-- Absolute value in the signed leading-term sort. -/
def rvAbs (hO : IsOrderConvex O) (t : RV0 O) : RV0 O :=
  letI := rvLinearOrder O hO
  if t < 0 then rv O (-1) * t else t

@[simp] theorem rvAbs_rv (hO : IsOrderConvex O) (x : K) :
    rvAbs O hO (rv O x) = rv O |x| := by
  by_cases hx : x < 0
  · rw [rvAbs, ite_eq_left ((rv_lt_zero_iff O hO).mpr hx), ← map_mul (rv O),
      neg_one_mul, abs_of_neg hx]
  · rw [rvAbs, ite_eq_right (fun ht => hx ((rv_lt_zero_iff O hO).mp ht)),
      abs_of_nonneg (not_lt.mp hx)]

/-- The valuation-ring test using only the reviewed RV order, absolute
value, and residue predicate. This is the test in Theorem 2.16. -/
theorem mem_valuationRing_iff_rvOrder (hO : IsOrderConvex O) (x : K) :
    letI := rvLinearOrder O hO
    x ∈ O ↔ rvAbs O hO (rv O x) ≤ 1 ∨ unsignedValue O (rv O x) = 1 := by
  rw [rvAbs_rv, unsignedValue_rv, ← map_one (rv O), rv_le_rv_iff O hO]
  rw [← O.valuation_le_one_iff]
  constructor
  · intro hx
    by_cases h : |x| ≤ 1
    · exact Or.inl (Or.inl h)
    · have hv := valuation_le_of_abs_le_abs O hO
        (show |(1 : K)| ≤ |x| by simpa only [abs_one] using (lt_of_not_ge h).le)
      rw [map_one] at hv
      exact Or.inr (hx.antisymm hv)
  · rintro ((h | h) | h)
    · have hv := valuation_le_of_abs_le_abs O hO (show |x| ≤ |(1 : K)| by simpa using h)
      simpa only [map_one] using hv
    · have hv := congrArg (unsignedValue O) h
      rw [unsignedValue_rv, unsignedValue_rv, map_one] at hv
      exact ((valuation_abs O x).symm.trans hv).le
    · exact h.le

end GeneralizedEuler.Section2
