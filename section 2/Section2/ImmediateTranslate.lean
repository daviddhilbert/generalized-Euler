module

public import Section2.ConvexRingComparison
public import Section2.TrivialBaseLift

/-! Matching translates and the new-leading-term dichotomy in Lemma 2.22. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO

set_option linter.style.haveILetI false in
/-- The signed leading terms of all translates determine the cut of
the adjunction over the old field. -/
theorem sameCut_of_equal_translate_rv {A : Set K} (f : A → K) {a b : K}
    (h : ∀ c : A, rv O (a - c.val) = rv O (b - f c)) (c : A) :
    (c.val < a ↔ f c < b) ∧ (a < c.val ↔ b < f c) := by
  letI := rvLinearOrder O hO
  constructor
  · calc
      c.val < a ↔ 0 < a - c.val := sub_pos.symm
      _ ↔ 0 < rv O (a - c.val) := (zero_lt_rv_iff O hO).symm
      _ ↔ 0 < rv O (b - f c) := by rw [h c]
      _ ↔ 0 < b - f c := zero_lt_rv_iff O hO
      _ ↔ f c < b := sub_pos
  · calc
      a < c.val ↔ a - c.val < 0 := sub_neg.symm
      _ ↔ rv O (a - c.val) < 0 := (rv_lt_zero_iff O hO).symm
      _ ↔ rv O (b - f c) < 0 := by rw [h c]
      _ ↔ b - f c < 0 := rv_lt_zero_iff O hO
      _ ↔ b < f c := sub_neg

/-- A changed RV sort has a new translated leading term in each of the
three cases of the proof. The fine valuation need only detect a new
value. In the weakly immediate case, the approved Tyne transfer rules
out a changed RV sort if all the translates have old leading terms. -/
theorem exists_new_translate_of_changed_fieldRV {A B : Subfield K} {a : K}
    (hAB : A ≤ B) (ha : a ∉ A) (hnew : fieldRV O B ≠ fieldRV O A)
    (detect : ∀ y ∈ B, O.valuation y ∉ O.valuation '' (A : Set K) →
      ∃ d ∈ A, O.valuation (a - d) ∉ O.valuation '' (A : Set K))
    (hresidueCase : WeakImmediacyTransfer O A B a ∨
      ∃ Q : ValuationSubring K, IsOrderConvex Q ∧
        ∃ y ∈ B, Q.valuation y ∉ Q.valuation '' (A : Set K) ∧
          (∀ z ∈ B, Q.valuation z ∉ Q.valuation '' (A : Set K) →
            ∃ d ∈ A, Q.valuation (a - d) ∉ Q.valuation '' (A : Set K))) :
    ∃ d ∈ A, rv O (a - d) ∉ fieldRV O A := by
  by_cases hv : ∃ y ∈ B, O.valuation y ∉ O.valuation '' (A : Set K)
  · obtain ⟨y, hy, hval⟩ := hv
    obtain ⟨d, hd, hdval⟩ := detect y hy hval
    refine ⟨d, hd, ?_⟩
    rintro ⟨x, hx, hxr⟩
    exact hdval ⟨x, hx, by simpa only [unsignedValue_rv] using congrArg (unsignedValue O) hxr⟩
  rcases hresidueCase with htyne | ⟨Q, hQ, y, hy, hval, hdetect⟩
  · by_contra! h
    exact hnew (fieldRV_eq_of_old_translates O hAB ha htyne h)
  · obtain ⟨d, hd, htranslate⟩ := hdetect y hy hval
    exact ⟨d, hd, rv_not_mem_range_of_new_fine_value O Q hO hQ htranslate⟩

omit hO [LinearOrder K] [IsStrictOrderedRing K] in
/-- A point outside a trivially valued base has a new leading term
after translation by at most one old representative. -/
theorem exists_new_translate_of_trivially_valued_field {A : Subfield K} {a : K}
    (ha : a ∉ A) (hTriv : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1) :
    ∃ d ∈ A, rv O (a - d) ∉ fieldRV O A := by
  by_cases h : rv O a ∈ fieldRV O A
  · obtain ⟨c, hc, he⟩ := h
    have ha0 : a ≠ 0 := fun hz => ha (hz.symm ▸ A.zero_mem)
    have hc0 : c ≠ 0 := by
      intro hz
      rw [hz, map_zero] at he
      exact ha0 ((rv_eq_zero_iff O).mp he.symm)
    have hv := (rv_eq_rv_iff_valuation O hc0).mp he.symm
    rw [hTriv c hc hc0] at hv
    refine ⟨c, hc, ?_⟩
    rintro ⟨d, hd, he⟩
    have hval := congrArg (unsignedValue O) he
    rw [unsignedValue_rv, unsignedValue_rv] at hval
    by_cases hd0 : d = 0
    · rw [hd0, map_zero] at he
      exact ha ((sub_eq_zero.mp ((rv_eq_zero_iff O).mp he.symm)) ▸ hc)
    · rw [hTriv d hd hd0] at hval
      exact hv.ne hval.symm
  · exact ⟨0, A.zero_mem, by simpa only [sub_zero] using h⟩

end GeneralizedEuler.Section2
