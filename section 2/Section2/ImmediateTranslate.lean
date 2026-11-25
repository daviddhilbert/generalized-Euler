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

end GeneralizedEuler.Section2
