module

public import Section5.RVObjectLifts
public import Section2.RVMonomials

/-! Define the multiplier interval over the original two-sorted base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

set_option linter.style.haveILetI false in
theorem small_multiplier_iff_signed_bounds (t : RV0 O) :
    letI := rvLinearOrder O hO
    unsignedValue O t < 1 ↔ (rv O (-1) ≤ t ∧ t ≤ 1) ∧ unsignedValue O t ≠ 1 := by
  letI := rvLinearOrder O hO
  obtain ⟨x,rfl⟩ := rv_surjective O t
  constructor
  · intro h
    have hm : x ∈ O := (O.valuation_le_one_iff x).1 (by
      rw [← unsignedValue_rv]
      exact h.le)
    have hB := (mem_valuationRing_iff_signed_bounds O hO x).1 hm
    exact ⟨hB.resolve_right h.ne,h.ne⟩
  · rintro ⟨bound,hn⟩
    have hm : x ∈ O := (mem_valuationRing_iff_signed_bounds O hO x).2 (Or.inl bound)
    rw [unsignedValue_rv] at hn ⊢
    exact ((O.valuation_le_one_iff x).2 hm).lt_of_ne hn

private def signedLE {W : TCsort → Type z} (a b : SortedTerm L E W .rv) : SortedFormula L E W :=
  .rel .rvLE (Fin.cases a (fun i => by
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst i
    exact b))

private theorem signedLE_realize {W : TCsort → Type z} (a b : SortedTerm L E W .rv)
    (v : ∀ s, W s → CanonicalSort O s) :
    (signedLE a b).realize 𝓜 v ↔ (rvLinearOrder O hO).le (a.realize 𝓜 v) (b.realize 𝓜 v) := by
  rfl

/-- Positive-degree multipliers are the nonzero part of the interval.
The excluded zero is definable over the same base. -/
theorem nonzero_multipliers_definable (hneg : rv O (-1) ∈ S.carrier .rv) :
    isRVSet 𝓜 S {x : Fin 1 → RV0 O | unsignedValue O (x 0) < 1 ∧ x 0 ≠ 0} := by
  let W := WithBase S.carrier (RVVariables (Fin 1))
  let t : SortedTerm L E W .rv := .var (.inr 0)
  let neg : SortedTerm L E W .rv := .var (.inl ⟨_,hneg⟩)
  let φ := ((signedLE neg t).conjunction (signedLE t rvOneTerm)).conjunction
    ((rvSameUnsignedValueFormula t rvOneTerm).neg.conjunction (SortedFormula.equal t rvZeroTerm).neg)
  refine ⟨φ,fun a => ?_⟩
  simp only [φ, SortedFormula.realize_conjunction, SortedFormula.realize_neg,
    signedLE_realize O hO power, realize_rvSameUnsignedValueFormula O hO power,
    SortedFormula.realize, realize_rvZeroTerm O hO power, t, neg, SortedTerm.realize]
  change (unsignedValue O (a .rv 0) < 1 ∧ a .rv 0 ≠ 0) ↔
    ((rvLinearOrder O hO).le (rv O (-1)) (a .rv 0) ∧
      (rvLinearOrder O hO).le (a .rv 0) 1) ∧
    (¬ unsignedValue O (a .rv 0) = unsignedValue O (1 : RV0 O) ∧ ¬a .rv 0 = 0)
  rw [map_one,small_multiplier_iff_signed_bounds O hO]
  exact and_assoc

end GeneralizedEuler.Section5
