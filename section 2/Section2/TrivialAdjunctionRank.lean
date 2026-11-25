module

public import Section2.WilkieInequality
public import Section2.TrivialBaseLift

/-! The rank alternatives over a trivially valued base from the
approved leading-term formula. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w} [Field E]
  {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  {graph : E → L.Formula (Fin 2)} (g : NamedFieldPowers K graph)
  (O : ValuationSubring K) (p : NamedRVPowers O g.pow)
  (A : Subfield K) (hStable : ∀ e (x : PositiveField K), (x : K) ∈ A → (g.pow e x : K) ∈ A)

set_option linter.style.haveILetI false in
/-- If the base is trivially valued, a monomial description by a
nonunit generator leaves the residue field unchanged. -/
theorem rv_mem_old_of_valuation_one_of_monomials
    (a : PositiveField K) (ha : O.valuation a.val ≠ 1)
    (hTriv : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1)
    (hNormal : ∀ x : K, x ≠ 0 → ∃ d ∈ A, ∃ e : E, rv O x = rv O d * p.pow e (rv O a.val))
    (x : K) (hx : O.valuation x = 1) : rv O x ∈ rv O '' (A : Set K) := by
  letI := unsignedValueModule O g.pow p.pow p.agrees g.zero g.one g.add g.mul p.units
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hx
    exact zero_ne_one hx
  obtain ⟨d, hd, e, he⟩ := hNormal x hx0
  have hv := congrArg (unsignedValue O) he
  rw [p.agrees e a, ← map_mul, unsignedValue_rv, unsignedValue_rv, map_mul, hx] at hv
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, map_zero, zero_mul] at hv
    exact one_ne_zero hv
  rw [hTriv d hd hd0, one_mul] at hv
  have hg : positiveFieldValue O (g.pow e a) = 0 := by
    apply Units.ext
    change ((positiveFieldValue O (g.pow e a)).toMul : O.ValueGroup) = 1
    rw [positiveFieldValue_coe]
    exact hv.symm
  have ha' : positiveFieldValue O a ≠ 0 := by
    intro h
    have hv' := congrArg (fun z : Additive (O.ValueGroupˣ) => (z.toMul : O.ValueGroup)) h
    rw [positiveFieldValue_coe] at hv'
    exact ha hv'
  have hsmul : e • positiveFieldValue O a = 0 :=
    (positiveFieldValue_power O g.pow p.pow p.agrees g.zero g.one g.add g.mul p.units e a).symm.trans hg
  obtain rfl | h := smul_eq_zero.mp hsmul
  · rw [p.agrees 0 a, g.zero, show ((1 : PositiveField K) : K) = 1 from rfl, map_one, mul_one (M := RV0 O)] at he
    exact ⟨d, hd, he.symm⟩
  · exact (ha' h).elim

/-- Both rank alternatives over the trivially valued old field.
The residue rank in the unit case is the ordinary rank in the
residue reduct of the trivially valued adjunction. -/
theorem nonempty_adjunctionRankData_of_trivial_base
    [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (a : PositiveField K) (hFresh : rv O a.val ∉ rv O '' (A : Set K))
    (hTriv : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1)
    (freni : LeadingTermMonomialTransfer O g.pow A ⊤ a.val)
    (freniInv : LeadingTermMonomialTransfer O g.pow A ⊤ ((a⁻¹ : PositiveField K) : K))
    (residue : ResiduePregeometryData O A L)
    (hRes : O.valuation a.val = 1 → residue.matroid.eRk residue.matroid.E ≤ 1) :
    Nonempty (AdjunctionRankData g O p A hStable a) := by
  have old_test : O.valuation a.val ∈ O.valuation '' (A : Set K) ↔ O.valuation a.val = 1 := by
    constructor
    · rintro ⟨c, hc, he⟩
      have hc0 : c ≠ 0 := by
        intro hz
        rw [hz, map_zero] at he
        exact ((map_ne_zero O.valuation).mpr a.property.ne') he.symm
      exact he.symm.trans (hTriv c hc hc0)
    · intro h
      exact ⟨1, A.one_mem, (map_one O.valuation).trans h.symm⟩
  have hValues (h : O.valuation a.val = 1) (x : K) : O.valuation x ∈ O.valuation '' (A : Set K) := by
    by_cases hx : x = 0
    · exact ⟨0, A.zero_mem, congrArg O.valuation hx.symm⟩
    · have hDetect (x : K) (hx : x ∈ (⊤ : Subfield K))
          (hv : O.valuation x ∉ O.valuation '' (A : Set K)) :
          ∃ d ∈ A, O.valuation (a.val - d) ∉ O.valuation '' (A : Set K) :=
        exists_translate_of_new_value O freni hStable
          (fun e x y h => power_respects_unsignedValue O (g.pow e) (p.units e) h) hx hv
      have hv := trivialBase_values_eq_of_new_residue O (B := ⊤) h hFresh hTriv hDetect x (by trivial) hx
      exact ⟨1, A.one_mem, (map_one O.valuation).trans hv.symm⟩
  have hNormal (h : O.valuation a.val ≠ 1) (x : K) (hx : x ≠ 0) :
      ∃ d ∈ A, ∃ e : E, rv O x = rv O d * p.pow e (rv O a.val) :=
    trivialBase_leadingTerm_of_value_ne_one O hO a (by trivial) h hTriv hStable p.agrees
      g.zero g.one g.add freni freniInv (by trivial) hx
  refine ⟨⟨residue, ?_, fun h => hValues (old_test.mp h), ?_, fun h => hRes (old_test.mp h)⟩⟩
  · by_cases h : O.valuation a.val = 1
    · exact relativeValueRankLEOne_of_old_values O g.pow g.zero g.one g.add g.mul A hStable
        p.pow p.agrees p.units (hValues h)
    · exact relativeValueRankLEOne_of_monomials O g.pow g.zero g.one g.add g.mul A hStable
        p.pow p.agrees p.units a (hNormal h)
  · intro h x hx
    have hn := old_test.not.mp h
    exact rv_mem_old_of_valuation_one_of_monomials g O p A a hn hTriv (hNormal hn) x hx

/-- The rank data used by the generated-field proof follow from
Wilkie over a nontrivial base and the leading-term formula over a
trivial base. -/
theorem nonempty_adjunctionRankData_of_cited_results
    [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (a : PositiveField K) (hFresh : rv O a.val ∉ rv O '' (A : Set K))
    (residue : ResiduePregeometryData O A L)
    (hWilkie : (¬ ∀ x ∈ A, x ≠ 0 → O.valuation x = 1) →
      OneGeneratorWilkieInequality g O p A hStable residue.matroid)
    (hFreni : (∀ x ∈ A, x ≠ 0 → O.valuation x = 1) →
      LeadingTermMonomialTransfer O g.pow A ⊤ a.val ∧
      LeadingTermMonomialTransfer O g.pow A ⊤ ((a⁻¹ : PositiveField K) : K))
    (hRes : (∀ x ∈ A, x ≠ 0 → O.valuation x = 1) →
      O.valuation a.val = 1 → residue.matroid.eRk residue.matroid.E ≤ 1) :
    Nonempty (AdjunctionRankData g O p A hStable a) := by
  by_cases h : ∀ x ∈ A, x ≠ 0 → O.valuation x = 1
  · obtain ⟨left, right⟩ := hFreni h
    exact nonempty_adjunctionRankData_of_trivial_base g O p A hStable hO a hFresh h
      left right residue (hRes h)
  · exact nonempty_adjunctionRankData_of_wilkie g O p A hStable a hFresh residue (hWilkie h)

/-- The named literature inputs on one side of a generated field
adjunction, including the ordinary residue rank in the trivial-unit case. -/
structure AdjunctionRankCitations [L.Structure (Residue O)] (a : PositiveField K) where
  residue : ResiduePregeometryData O A L
  wilkie : (¬ ∀ x ∈ A, x ≠ 0 → O.valuation x = 1) →
    OneGeneratorWilkieInequality g O p A hStable residue.matroid
  freni : (∀ x ∈ A, x ≠ 0 → O.valuation x = 1) →
    LeadingTermMonomialTransfer O g.pow A ⊤ a.val ∧
    LeadingTermMonomialTransfer O g.pow A ⊤ ((a⁻¹ : PositiveField K) : K)
  residueRank : (∀ x ∈ A, x ≠ 0 → O.valuation x = 1) →
    O.valuation a.val = 1 → residue.matroid.eRk residue.matroid.E ≤ 1

theorem AdjunctionRankCitations.nonempty_rankData
    [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (a : PositiveField K) (hFresh : rv O a.val ∉ rv O '' (A : Set K))
    (data : AdjunctionRankCitations g O p A hStable a) :
    Nonempty (AdjunctionRankData g O p A hStable a) :=
  nonempty_adjunctionRankData_of_cited_results g O p A hStable hO a hFresh data.residue
    data.wilkie data.freni data.residueRank

end GeneralizedEuler.Section2
