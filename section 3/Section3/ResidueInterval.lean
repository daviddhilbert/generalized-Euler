module

public import Section3.NormalizedSlice
public import Mathlib.Algebra.Order.Group.Pointwise.Interval

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- One nondegenerate secant and the constant value of the normalized
field derivative imply integrality of the derivative on the whole branch. -/
theorem integral_derivative_on_branch (A : Set O) (F : O → O) (d : O → K)
    {a b : O} (ha : a ∈ A) (hb : b ∈ A) (hne : IsLocalRing.residue O a ≠ IsLocalRing.residue O b)
    (value : ∀ x ∈ A, ∀ y ∈ A, O.valuation (d x) = O.valuation (d y))
    (mvt : ∀ x ∈ A, ∀ y ∈ A, IsLocalRing.residue O x ≠ IsLocalRing.residue O y →
      ∃ c ∈ A, (F y : K) - F x = ((y : K) - x) * d c) : ∀ x ∈ A, d x ∈ O := by
  obtain ⟨c,hc,he⟩ := mvt a ha b hb hne
  have hd := integral_of_mean_value O hne he
  intro x hx
  rwa [←O.valuation_le_one_iff,value x hx c hc,O.valuation_le_one_iff]

/-- On a residue interval the ordinary field mean value theorem yields
the order derivative of the contracted function. All representatives are
quantified. This is the adjacent-partial estimate used in 3.30 and 3.31. -/
theorem derivative_on_residue_interval (U : Set (Residue O)) (F d : O → O)
    (G H : Residue O → Residue O) (r : Residue O) (hr : r ∈ U)
    (contrF : ∀ x : O, IsLocalRing.residue O x ∈ U →
      IsLocalRing.residue O (F x) = G (IsLocalRing.residue O x))
    (contrD : ∀ x : O, IsLocalRing.residue O x ∈ U →
      IsLocalRing.residue O (d x) = H (IsLocalRing.residue O x)) :
    letI := residueLinearOrder O hO
    (∃ δ > 0, ∀ h : Residue O, |h| < δ → r+h ∈ U) →
    (∀ ε > 0, ∃ δ > 0, ∀ s ∈ U, |s-r| < δ → |H s-H r| < ε) →
    (∀ x y : O, IsLocalRing.residue O x ∈ U → IsLocalRing.residue O y ∈ U →
      IsLocalRing.residue O x ≠ IsLocalRing.residue O y →
      ∃ z ∈ uIcc x y, IsLocalRing.residue O z ∈ U ∧
        (F y : K) - F x = ((y : K)-x) * d z) →
    HasOrderDerivativeAt G r (H r) := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  rintro ⟨δ₀,hδ₀,hU⟩ hc hmvt
  apply hasOrderDerivativeAt_of_secants G H r
  · intro ε hε
    obtain ⟨δ,hδ,hcont⟩ := hc ε hε
    refine ⟨min δ₀ δ,lt_min hδ₀ hδ,fun s hs => hcont s ?_ (hs.trans_le (min_le_right _ _))⟩
    simpa using hU (s-r) (hs.trans_le (min_le_left _ _))
  · refine ⟨δ₀,hδ₀,?_⟩
    intro h hn hsmall
    obtain ⟨x,hx⟩ := IsLocalRing.residue_surjective r
    obtain ⟨y,hy⟩ := IsLocalRing.residue_surjective (r+h)
    have hxU := hx.symm ▸ hr
    have hyU := hy.symm ▸ hU h hsmall
    have hxy : IsLocalRing.residue O x ≠ IsLocalRing.residue O y := by simpa [hx,hy] using hn
    obtain ⟨z,hz,hzU,he⟩ := hmvt x y hxU hyU hxy
    have hm := (residue_monotone O hO).mapsTo_uIcc hz
    rw [hx,hy] at hm
    refine ⟨IsLocalRing.residue O z,by simpa using abs_sub_left_of_mem_uIcc hm,?_⟩
    have eqn := residue_secant_eq O hxy he
    rwa [contrF x hxU,contrF y hyU,hx,hy,add_sub_cancel_left,contrD z hzU] at eqn

end GeneralizedEuler.Section3
