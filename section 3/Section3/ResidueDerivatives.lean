module

public import Section2.ResidueOrder
public import Section2.TorsorDerivative
import all Section2.TorsorDerivative
public import Mathlib.Algebra.MvPolynomial.CommRing

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- The normalized mean-value equation of 3.30 forces an integral
derivative at the intermediate point, because the horizontal difference is a unit. -/
theorem integral_of_mean_value {a b u v : O} {d : K}
    (hne : IsLocalRing.residue O a ≠ IsLocalRing.residue O b)
    (hm : (v : K) - u = ((b : K) - a) * d) : d ∈ O := by
  have hunit : IsUnit (b - a) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    (by rw [map_sub]; exact sub_ne_zero.mpr hne.symm)
  have he := (O.valuation_eq_one_iff _).mp hunit
  have hval := congrArg O.valuation hm
  rw [map_mul, show O.valuation ((b : K) - a) = 1 from he, one_mul] at hval
  exact (O.valuation_le_one_iff _).mp (hval ▸ O.valuation_le_one (v - u))

theorem residue_secant_eq {a b u v d : O}
    (hne : IsLocalRing.residue O a ≠ IsLocalRing.residue O b)
    (hm : (v : K) - u = ((b : K) - a) * d) :
    (IsLocalRing.residue O v - IsLocalRing.residue O u) /
      (IsLocalRing.residue O b - IsLocalRing.residue O a) = IsLocalRing.residue O d := by
  have h : v - u = (b - a) * d := Subtype.ext hm
  apply (div_eq_iff (sub_ne_zero.mpr hne.symm)).mpr
  simpa only [map_sub, map_mul, mul_comm] using congrArg (IsLocalRing.residue O) h

/-- The local limit argument uses the order-field derivative of Section 2.
A continuous reduced derivative bounding each secant at an intermediate
residue is the derivative of the reduced function. -/
theorem hasOrderDerivativeAt_of_secants [LinearOrder K] [IsStrictOrderedRing K]
    (G H : K → K) (x : K)
    (hcont : ∀ ε > 0, ∃ δ > 0, ∀ u, |u - x| < δ → |H u - H x| < ε)
    (hsec : ∃ r > 0, ∀ h : K, h ≠ 0 → |h| < r →
      ∃ u, |u - x| ≤ |h| ∧ (G (x + h) - G x) / h = H u) :
    HasOrderDerivativeAt G x (H x) := by
  obtain ⟨r, hr, hsec⟩ := hsec
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := hcont ε hε
  refine ⟨min r δ, lt_min hr hδ, ?_⟩
  intro h hne hsmall
  obtain ⟨u, hu, he⟩ := hsec h hne (lt_min_iff.mp hsmall).1
  rw [he]
  exact hcont u (hu.trans_lt (lt_min_iff.mp hsmall).2)

/-- Corollary 3.32 on a common good label. The variables of P index the
finitely many jets it uses. Coefficient reduction and the adjacently
proved derivative identities give the claimed value. -/
theorem residue_differential_polynomial {J : Type*} (P : MvPolynomial J O)
    (jet : J → O) (reducedJet : J → Residue O)
    (hjet : ∀ j, IsLocalRing.residue O (jet j) = reducedJet j) :
    IsLocalRing.residue O (MvPolynomial.eval jet P) =
      MvPolynomial.eval reducedJet (MvPolynomial.map (IsLocalRing.residue O) P) := by
  rw [← show (IsLocalRing.residue O) ∘ jet = reducedJet from funext hjet]
  exact MvPolynomial.map_eval _ _ _

end GeneralizedEuler.Section3
