module

public import Section2.DiscCodes
public import Section2.LeadingTermOrder

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO

/-- At the right end of an open disc the distances to its fixed center
eventually exceed each prescribed smaller value. Values are multiplicative. -/
theorem larger_value_on_upper_tail {a x : K} {r t : O.ValueGroup}
    [DenselyOrdered O.ValueGroup] (hx : x ∈ openDisc O a r) (ht : t < r) :
    ∃ y ∈ openDisc O a r, x < y ∧ t < O.valuation (y - a) := by
  obtain ⟨s,hs,hsr⟩ := exists_between (max_lt (show O.valuation (x - a) < r from hx) ht)
  obtain ⟨d,hd⟩ := O.valuation_surjective s
  have hxd : |x-a| < |d| := by
    by_contra! h
    have hle := valuation_le_of_abs_le_abs O hO h
    exact ((le_max_left _ _).trans_lt hs).not_ge (hd ▸ hle)
  have he : O.valuation (a + |d| - a) = s := by rw [add_sub_cancel_left,valuation_abs,hd]
  refine ⟨a + |d|,he.trans_lt hsr,?_,(le_max_right _ _).trans_lt hs |>.trans_eq he.symm⟩
  linarith [le_abs_self (x-a)]

/-- The cofinal tail of the inverse in 3.13 cannot satisfy the eventual
constant-value assertion of 3.2. Cofinality is required after *every*
input cutoff, as supplied by a monotone inverse approaching the upper end. -/
theorem not_eventually_constant_of_disc_end {I : Type*} [LinearOrder I] [Nonempty I]
    {r : O.ValueGroup} [DenselyOrdered O.ValueGroup] (f : I → K) (a : K)
    (hf : ∀ b, f b ∈ openDisc O a r)
    (hcof : ∀ b : I, ∀ x ∈ openDisc O a r, ∃ c ≥ b, x ≤ f c) :
    ¬ ∃ b, ∀ c ≥ b, O.valuation (f c - a) = O.valuation (f b - a) := by
  rintro ⟨b,hb⟩
  obtain ⟨y,hy,_,hyval⟩ := larger_value_on_upper_tail O hO (hf b)
    (show O.valuation (f b - a) < r from hf b)
  have ha : a ∈ openDisc O a r := mem_openDisc_center O (zero_le.trans_lt
    (show O.valuation (f b - a) < r from hf b)).ne' a
  obtain ⟨z,hz,haz,hzval⟩ := larger_value_on_upper_tail O hO ha
    (show O.valuation (y - a) < r from hy)
  obtain ⟨c,hc,hcz⟩ := hcof b z hz
  have hmon := valuation_le_of_nonneg_le O hO (sub_nonneg.mpr haz.le)
    (sub_le_sub_right hcz a)
  rw [hb c hc] at hmon
  exact (hyval.trans hzval).not_ge hmon

end GeneralizedEuler.Section3
