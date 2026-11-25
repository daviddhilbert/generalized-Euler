module

public import Section2.LeadingTermOrder
public import Section2.ValueSplitting

/-! Comparison of convex valuation rings in the prescribed-lift proof. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O P : ValuationSubring K)

private theorem mem_of_abs_le_mem {x y : K} (hO : IsOrderConvex O) (hy : y ∈ O)
    (hxy : |x| ≤ |y|) : x ∈ O := by
  have habs : |y| ∈ O := by
    rcases le_or_gt 0 y with h | h
    · simpa only [abs_of_nonneg h] using hy
    · simpa only [abs_of_neg h] using O.neg_mem y hy
  exact hO.out (O.neg_mem _ habs) habs (abs_le.mp hxy)

/-- Convex valuation rings of the same ordered field are comparable. -/
theorem convexValuationRing_comparable (hO : IsOrderConvex O) (hP : IsOrderConvex P) :
    O ≤ P ∨ P ≤ O := by
  by_cases h : O ≤ P
  · exact Or.inl h
  right
  have hh : ¬ ∀ x : K, x ∈ O → x ∈ P := h
  rw [not_forall] at hh
  obtain ⟨x, hx⟩ := hh
  have hxO : x ∈ O := by
    by_contra h
    exact hx (fun ha => (h ha).elim)
  have hxP : x ∉ P := fun hp => hx (fun _ => hp)
  intro y hy
  rcases le_total |y| |x| with h | h
  · exact mem_of_abs_le_mem O hO hxO h
  · exact (hxP (mem_of_abs_le_mem P hP hy h)).elim

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- If the value-group map of a coarsening is injective, the two valuation
rings coincide. -/
theorem eq_of_injective_valueCoarsening (h : O ≤ P)
    (hinj : Function.Injective (ValuationSubring.mapOfLE O P h)) : O = P := by
  apply le_antisymm h
  intro x hx
  by_contra ho
  have hv : 1 < O.valuation x := by
    apply lt_of_not_ge
    exact fun hx' => ho ((O.valuation_le_one_iff x).mp hx')
  have hle : 1 ≤ P.valuation x := by
    have hm := ValuationSubring.monotone_mapOfLE O P h hv.le
    simpa only [map_one, ValuationSubring.mapOfLE_valuation_apply] using hm
  have heq : P.valuation x = 1 := ((P.valuation_le_one_iff x).mpr hx).antisymm hle
  have hm : ValuationSubring.mapOfLE O P h (O.valuation x) =
      ValuationSubring.mapOfLE O P h 1 := by
    rw [ValuationSubring.mapOfLE_valuation_apply, map_one, heq]
  exact hv.ne' (hinj hm)

/-- Linear maps out of a one-dimensional exponent space are injective
when they retain its nonzero generator. -/
theorem injective_valueMap_of_span_singleton
    {E V W : Type*} [Field E] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]
    (f : V →ₗ[E] W) {a : V} (hspan : Submodule.span E {a} = ⊤) (ha : f a ≠ 0) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  refine eq_bot_iff.mpr ?_
  intro x hx
  have hm : x ∈ Submodule.span E {a} := hspan ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
  have hzero := LinearMap.mem_ker.mp hx
  rw [← hr, map_smul] at hzero
  have hr0 : r = 0 := (smul_eq_zero.mp hzero).resolve_right ha
  rw [← hr, hr0, zero_smul]
  exact Submodule.zero_mem _

end GeneralizedEuler.Section2
