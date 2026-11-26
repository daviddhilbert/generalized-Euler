module

public import Section3.AffineSlopes
public import Section3.DiscMaps
import all Section3.AffineSlopes

/-! A bijection between discs with a nonzero affine RV slope is
disc-to-disc. The first-order chart test then needs only the source
and target disc conditions and the affine graph. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {A B : Set K} {f g : K → K} {s : O.ValueGroup}

theorem concentric_of_affine_bijection
    (bij : Set.BijOn f A B) (affine : ValAffineOn O A f s) (scale : s ≠ 0)
    (target : ∀ c ∈ A, ∀ r, r ≠ 0 → openDisc O c r ⊆ A →
      openDisc O (f c) (s*r) ⊆ B) : ConcentricOn O A f := by
  intro c r rn sub
  have hc : c ∈ A := sub (mem_openDisc_center O rn c)
  have p : 0 < s := pos_iff_ne_zero.2 scale
  have image : f '' openDisc O c r = openDisc O (f c) (s*r) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change O.valuation (f x-f c) < s*r
      rw [affine x (sub hx) c hc]
      exact mul_lt_mul_of_pos_left hx p
    · intro hy
      obtain ⟨x,hx,rfl⟩ := bij.surjOn (target c hc r rn sub hy)
      change O.valuation (f x-f c) < s*r at hy
      rw [affine x hx c hc] at hy
      exact ⟨x,(mul_lt_mul_iff_of_pos_left p).1 hy,rfl⟩
  exact ⟨f c,s*r,mul_ne_zero scale rn,image⟩

theorem DiscToDiscOn_of_affine_discs
    {a b : K} {r t : O.ValueGroup} (rn : r ≠ 0) (sn : s ≠ 0)
    (bij : Set.BijOn f (openDisc O a r) (openDisc O b t))
    (inverse : Set.InvOn g f (openDisc O a r) (openDisc O b t))
    (affine : ValAffineOn O (openDisc O a r) f s) :
    DiscToDiscOn O (openDisc O a r) (openDisc O b t) f g := by
  let A := openDisc O a r
  let B := openDisc O b t
  have radii := radius_eq_shift_mul O rn sn bij.image_eq affine
  have toSub {a c : K} {r z : O.ValueGroup} (hc : c ∈ openDisc O a r)
      (sub : openDisc O c z ⊆ openDisc O a r) : z ≤ r := by
    have ball : openDisc O c z ⊆ openDisc O c r := (openDisc_change_center O hc).symm ▸ sub
    by_contra! h
    obtain ⟨x,hx,eq⟩ := (Set.ext_iff.mp (openDisc_difference_values O c z) r).2 h
    have less : O.valuation (x-c) < r := ball hx
    change O.valuation (x-c) = r at eq
    rw [eq] at less
    exact (lt_irrefl _) less
  have forward : ConcentricOn O A f := by
    apply concentric_of_affine_bijection O bij affine sn
    intro c hc z nz sub q hq
    have h := toSub hc sub
    change q ∈ openDisc O b t
    rw [← openDisc_change_center O (bij.mapsTo hc),radii]
    exact (show O.valuation (q-f c) < s*z from hq).trans_le
      (mul_le_mul_of_nonneg_left h zero_le)
  have back : Set.BijOn g B A := by
    refine ⟨?_,?_,?_⟩
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := bij.surjOn hy
      exact (inverse.1 hx).symm ▸ hx
    · intro y hy z hz e
      exact (inverse.2 hy).symm.trans ((congrArg f e).trans (inverse.2 hz))
    · intro x hx
      exact ⟨f x,bij.mapsTo hx,inverse.1 hx⟩
  have reverseAffine : ValAffineOn O B g s⁻¹ := by
    intro x hx y hy
    have e := affine (g x) (back.mapsTo hx) (g y) (back.mapsTo hy)
    rw [inverse.2 hx,inverse.2 hy] at e
    rw [e,← mul_assoc,inv_mul_cancel₀ sn,one_mul]
  have backward : ConcentricOn O B g := by
    apply concentric_of_affine_bijection O back reverseAffine (inv_ne_zero sn)
    intro c hc z nz sub q hq
    have h := toSub hc sub
    change q ∈ openDisc O a r
    rw [← openDisc_change_center O (back.mapsTo hc)]
    have rr : s⁻¹*t = r := by rw [radii,← mul_assoc,inv_mul_cancel₀ sn,one_mul]
    exact (show O.valuation (q-g c) < s⁻¹*z from hq).trans_le
      (rr ▸ mul_le_mul_of_nonneg_left h zero_le)
  exact ⟨bij,inverse,forward,backward⟩

end GeneralizedEuler.Section5
