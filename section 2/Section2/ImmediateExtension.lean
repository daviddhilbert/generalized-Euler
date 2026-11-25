module

public import Section2.LeadingTermMap
public import Section2.LeadingTermPower

/-! Valuation calculations in the reviewed proof of Lemma 2.22. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- The set of leading terms represented in a field substructure. -/
@[expose]
def fieldRV (A : Subfield K) : Set (RV0 O) := rv O '' (A : Set K)

/-- Weak immediacy in the multiplicative value convention. Every
approximation by the base can be improved. -/
def IsWeaklyImmediate (A : Subfield K) (a : K) : Prop :=
  ∀ c ∈ A, ∃ d ∈ A, O.valuation (a - d) < O.valuation (a - c)

theorem weaklyImmediate_of_old_translates {A : Subfield K} {a : K} (ha : a ∉ A)
    (h : ∀ c ∈ A, rv O (a - c) ∈ fieldRV O A) :
    IsWeaklyImmediate O A a := by
  intro c hc
  obtain ⟨e, he, hrv⟩ := h c hc
  have hac : a - c ≠ 0 := sub_ne_zero.mpr (fun hac => ha (hac.symm ▸ hc))
  refine ⟨c + e, A.add_mem hc he, ?_⟩
  have hv := (rv_eq_rv_iff_valuation O hac).mp hrv
  rw [sub_add_eq_sub_sub, ← neg_sub e, O.valuation.map_neg]
  exact hv

theorem old_translates_of_weaklyImmediate {A : Subfield K} {a : K}
    (h : IsWeaklyImmediate O A a) (c : K) (hc : c ∈ A) :
    rv O (a - c) ∈ fieldRV O A := by
  obtain ⟨d, hd, hv⟩ := h c hc
  have hac : a - c ≠ 0 := by
    intro hac
    rw [hac, map_zero] at hv
    exact (not_lt_of_ge zero_le) hv
  refine ⟨d - c, A.sub_mem hd hc, (rv_eq_rv_iff_valuation O hac).mpr ?_⟩
  rw [sub_sub_sub_cancel_right, ← neg_sub a, O.valuation.map_neg]
  exact hv

/-- The input from Freni, Proposition 3.3.11 (Tyne), for a specified
one-generator elementary extension. Its hypotheses about the ambient
power-bounded T-structure belong to the application of this input. -/
def WeakImmediacyTransfer (A B : Subfield K) (a : K) : Prop :=
  IsWeaklyImmediate O A a → ∀ y ∈ B, y ∉ A → IsWeaklyImmediate O A y

/-- In the no-new-translate case, Tyne's result gives equality of the entire
RV images. This includes preservation of both values and residues. -/
theorem fieldRV_eq_of_old_translates {A B : Subfield K} {a : K}
    (hab : A ≤ B) (ha : a ∉ A) (htyne : WeakImmediacyTransfer O A B a)
    (h : ∀ c ∈ A, rv O (a - c) ∈ fieldRV O A) :
    fieldRV O B = fieldRV O A := by
  have hweak := htyne (weaklyImmediate_of_old_translates O ha h)
  apply Set.Subset.antisymm
  · rintro t ⟨y, hy, rfl⟩
    by_cases hyA : y ∈ A
    · exact ⟨y, hyA, rfl⟩
    · simpa only [sub_zero] using
        old_translates_of_weaklyImmediate O (hweak y hy hyA) 0 A.zero_mem
  · exact Set.image_mono hab

/-- Over a trivially valued base, a new field element has a translate
with a new leading term. This is the first step of the trivial-base case
of Lemma 2.22. -/
theorem exists_new_translate_of_trivial_base {A : Subfield K} {a : K} (ha : a ∉ A)
    (htriv : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1) :
    ∃ d ∈ A, rv O (a - d) ∉ fieldRV O A := by
  by_cases h : rv O a ∈ fieldRV O A
  · obtain ⟨c, hc, hrv⟩ := h
    have ha0 : a ≠ 0 := fun he => ha (he.symm ▸ A.zero_mem)
    have hc0 : c ≠ 0 := by
      intro he
      rw [he, map_zero, eq_comm, rv_eq_zero_iff] at hrv
      exact ha0 hrv
    refine ⟨c, hc, ?_⟩
    rintro ⟨d, hd, hrd⟩
    have hval : O.valuation (a - c) < 1 := by
      simpa only [htriv c hc hc0] using (rv_eq_rv_iff_valuation O hc0).mp hrv.symm
    have hd0 : d ≠ 0 := by
      intro he
      rw [he, map_zero, eq_comm, rv_eq_zero_iff, sub_eq_zero] at hrd
      exact ha (hrd.symm ▸ hc)
    have hvalue := congrArg (unsignedValue O) hrd
    rw [unsignedValue_rv, unsignedValue_rv, htriv d hd hd0] at hvalue
    exact (ne_of_lt hval) hvalue.symm
  · exact ⟨0, A.zero_mem, by simpa only [sub_zero]⟩

end GeneralizedEuler.Section2
