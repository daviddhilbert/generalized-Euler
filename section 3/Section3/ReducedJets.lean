module

public import Section3.SliceExceptions
import all Section3.NormalizedSlice
import all Section2.TorsorDerivative

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]

private theorem derivative_const_mul {G : k → k} {r s : k} (hd : HasOrderDerivativeAt G r s) (c : k) :
    HasOrderDerivativeAt (fun x => c * G x) r (c*s) := by
  by_cases hc : c = 0
  · subst c
    intro eps he
    exact ⟨1,zero_lt_one,fun h _ _ => by simpa using he⟩
  · simpa using hd.affine_change 1 c 0 0 one_ne_zero hc

theorem derivative_of_agreement_near {G H : k → k} {r s δ : k}
    (hd : HasOrderDerivativeAt G r s) (positive : 0 < δ)
    (equal : ∀ h : k, |h| < δ → G (r+h) = H (r+h)) : HasOrderDerivativeAt H r s := by
  have base : G r = H r := by simpa using equal 0 (by simpa using positive)
  intro eps he
  obtain ⟨e,ep,hs⟩ := hd eps he
  refine ⟨min δ e,lt_min positive ep,fun h hn hnear => ?_⟩
  rw [←equal h (hnear.trans_le (min_le_left _ _)),←base]
  exact hs h hn (hnear.trans_le (min_le_right _ _))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (O : ValuationSubring K) (hO : IsOrderConvex O)

/-- The two alternatives of 3.31 on a nonzero output chart. For the
strict-value alternative the normalized derivative is zero. For equal
values the nonzero chart derivative recovers the actual leading term
after scaling back by c. The valuation here is multiplicative. -/
theorem normalized_jet_alternatives {A : Set O} (g d : O → K) {c : K} (hc : c ≠ 0)
    (value : ∀ x ∈ A, O.valuation (g x) = O.valuation c) (r : Residue O)
    (good : NormalizedSliceAt O hO A g d c r) :
    letI := residueLinearOrder O hO
    ∃ G : Residue O → Residue O,
      (∀ x ∈ A, ∃ v : O, (v : K) = g x/c ∧ IsLocalRing.residue O v = G (IsLocalRing.residue O x)) ∧
      ∀ x ∈ A, IsLocalRing.residue O x = r →
        (O.valuation (d x) ≤ O.valuation (g x)) ∧
        ((d x = 0 ∨ O.valuation (d x) < O.valuation (g x)) ↔ HasOrderDerivativeAt G r 0) ∧
        (¬ (d x = 0 ∨ O.valuation (d x) < O.valuation (g x)) ↔
          ∃ s : Residue O, s ≠ 0 ∧ HasOrderDerivativeAt G r s ∧ rv O (d x) = rv O c * residueRV O s) := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  obtain ⟨G,hG,hD⟩ := good
  refine ⟨G,hG,fun x hx hxr => ?_⟩
  obtain ⟨v,hv,hd⟩ := hD x hx hxr
  have prod : d x = c * (v : K) := by rw [hv,mul_div_cancel₀ _ hc]
  have cp := pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hc : O.valuation c ≠ 0)
  have ltv : IsLocalRing.residue O v = 0 ↔ O.valuation (v : K) < 1 := by
    simpa using residue_eq_iff_valuation_sub_lt_one O v 0
  have small : d x = 0 ∨ O.valuation (d x) < O.valuation (g x) ↔ IsLocalRing.residue O v = 0 := by
    rw [ltv,prod,map_mul,value x hx]
    have cmp : O.valuation c * O.valuation (v : K) < O.valuation c ↔ O.valuation (v : K) < 1 := by
      conv_lhs => rhs; rw [←mul_one (O.valuation c)]
      exact mul_lt_mul_iff_of_pos_left cp
    rw [cmp]
    exact ⟨fun h => h.elim (fun h => by rw [(mul_eq_zero.mp h).resolve_left hc,map_zero]; exact zero_lt_one) id,Or.inr⟩
  refine ⟨?_,small.trans ⟨fun h => h ▸ hd,fun h => hd.unique h⟩,?_⟩
  · rw [value x hx,prod,map_mul]
    exact mul_le_of_le_one_right cp.le (O.valuation_le_one v)
  · rw [small]
    exact ⟨fun h => ⟨_,h,hd,by rw [prod,map_mul,residueRV_residue_of_ne_zero O v h]⟩,
      fun ⟨s,hs,hsd,_⟩ h => hs ((hd.unique hsd).symm.trans h)⟩

/-- Scaling back a successful adjacent-partial test gives integrality
and the derivative identity in residue coordinates. A scale from the
maximal ideal is allowed: its residue multiplies the entire germ by zero. -/
theorem reduce_adjacent_jet {A : Set O} (g : O → O) (d : O → K) (c : O) (hc : (c : K) ≠ 0)
    (G : Residue O → Residue O) (r : Residue O)
    (contr : ∀ x ∈ A, IsLocalRing.residue O (g x) = G (IsLocalRing.residue O x))
    (good : NormalizedSliceAt O hO A (fun x => (g x : K)) d (c : K) r) :
    letI := residueLinearOrder O hO
    (∃ δ > 0, ∀ h : Residue O, |h| < δ → ∃ x ∈ A, IsLocalRing.residue O x = r+h) →
    ∀ x ∈ A, IsLocalRing.residue O x = r →
      ∃ w : O, (w : K) = d x ∧ HasOrderDerivativeAt G r (IsLocalRing.residue O w) := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  rintro ⟨δ,hδ,fill⟩ x hx hxr
  obtain ⟨H,hH,test⟩ := good
  obtain ⟨w,hw,der⟩ := test x hx hxr
  have eqv {u : K} {z : O} (hz : (z : K) = u / c) : ((c*z : O) : K) = u := by
    change (c : K)*(z : K) = u
    rw [hz,mul_div_cancel₀ _ hc]
  refine ⟨c*w,eqv hw,?_⟩
  rw [map_mul]
  apply derivative_of_agreement_near (derivative_const_mul der (IsLocalRing.residue O c)) hδ
  intro h hh
  obtain ⟨a,ha,hr⟩ := fill h hh
  obtain ⟨z,hz,hred⟩ := hH a ha
  have eqg : c*z = g a := Subtype.ext (eqv hz)
  rw [←hr,←hred,←map_mul,eqg,contr _ ha]

end GeneralizedEuler.Section3
