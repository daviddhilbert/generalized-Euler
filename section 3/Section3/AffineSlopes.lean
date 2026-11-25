module

public import Section2.DiscCodes

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- Definition 3.35, with the nonzero slope in RV. -/
def RVAffineOn (A : Set K) (f : K → K) (t : RV O) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, rv O (f a - f b) = (t : RV0 O) * rv O (a - b)

def ValAffineOn (A : Set K) (f : K → K) (s : O.ValueGroup) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, O.valuation (f a - f b) = s * O.valuation (a - b)

theorem RVAffineOn.toValAffine {A : Set K} {f : K → K} {t : RV O}
    (h : RVAffineOn O A f t) : ValAffineOn O A f (unsignedValueUnit O t) := by
  intro a ha b hb
  simpa using congrArg (unsignedValue O) (h a ha b hb)

theorem RVAffineOn.unique {A : Set K} (hA : A.Nontrivial) {f : K → K} {s t : RV O}
    (hs : RVAffineOn O A f s) (ht : RVAffineOn O A f t) : s = t := by
  obtain ⟨a, ha, b, hb, hab⟩ := hA
  have h := (hs a ha b hb).symm.trans (ht a ha b hb)
  rw [mul_comm (G := RV0 O) (s : RV0 O), mul_comm (G := RV0 O) (t : RV0 O)] at h
  exact WithZero.coe_inj.mp (rv_mul_left_cancel O (by simpa using sub_ne_zero.mpr hab) h)

theorem ValAffineOn.unique {A : Set K} (hA : A.Nontrivial) {f : K → K}
    {s t : O.ValueGroup} (hs : ValAffineOn O A f s) (ht : ValAffineOn O A f t) : s = t := by
  obtain ⟨a, ha, b, hb, hab⟩ := hA
  exact mul_right_cancel₀ ((map_ne_zero O.valuation).mpr (sub_ne_zero.mpr hab))
    ((hs a ha b hb).symm.trans (ht a ha b hb))

/-- Value differences in an open disc exhaust the strict initial segment.
The center is fixed, so no definable choice of centers is needed. -/
theorem openDisc_difference_values (c : K) (r : O.ValueGroup) :
    (fun x => O.valuation (x - c)) '' openDisc O c r = Set.Iio r := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hv
    obtain ⟨x, rfl⟩ := O.valuation_surjective v
    exact ⟨x + c, by simpa [openDisc] using hv, by simp⟩

/-- Surjectivity identifies the two radii in 3.36. In multiplicative
notation the target radius is the source radius times the shift. -/
theorem radius_eq_shift_mul {a b : K} {r s k : O.ValueGroup} (hr : r ≠ 0)
    (hk : k ≠ 0) {f : K → K} (hf : f '' openDisc O a r = openDisc O b s)
    (hv : ValAffineOn O (openDisc O a r) f k) : s = k * r := by
  have ha := mem_openDisc_center O hr a
  have hb : f a ∈ openDisc O b s := hf ▸ Set.mem_image_of_mem f ha
  have h := openDisc_difference_values O (f a) s
  rw [openDisc_change_center O hb, ← hf, Set.image_image] at h
  have hmap : (fun x => O.valuation (f x - f a)) '' openDisc O a r =
      (fun v => k * v) '' Set.Iio r := by
    rw [← openDisc_difference_values O a r, Set.image_image]
    exact Set.image_congr (fun x hx => hv x hx a ha)
  have he := h.symm.trans hmap
  have hmem (v : O.ValueGroup) : v < s ↔ v < k * r := by
    change v ∈ Set.Iio s ↔ _
    rw [he]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact mul_lt_mul_of_pos_left hw (pos_iff_ne_zero.mpr hk)
    · intro hv'
      refine ⟨v / k, (div_lt_iff₀ (pos_iff_ne_zero.mpr hk)).mpr ?_, ?_⟩
      · simpa [mul_comm] using hv'
      · exact mul_div_cancel₀ _ hk
  exact le_antisymm (le_of_not_gt (fun hlt => (lt_irrefl _ ((hmem _).mp hlt))))
    (le_of_not_gt (fun hlt => (lt_irrefl _ ((hmem _).mpr hlt))))

/-- The mean-value step in 3.36. Use the definable mean value theorem on
each segment of the single field branch chosen on the atomic disc. -/
theorem rvAffine_of_mean_value {A : Set K} {f d : K → K} {t : RV O}
    (hder : ∀ x ∈ A, rv O (d x) = (t : RV0 O))
    (hmvt : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ c ∈ A, f a - f b = d c * (a - b)) :
    RVAffineOn O A f t := by
  intro a ha b hb
  by_cases he : a = b
  · simp [he, mul_zero (M₀ := RV0 O)]
  obtain ⟨c, hc, h⟩ := hmvt a ha b hb he
  rw [h, map_mul, hder c hc]

/-- Lemma 3.36 after choosing the differentiable branch and showing its derivative
has constant leading term. Injectivity on one pair forces that term to be nonzero.
Surjectivity then recovers the target radius from the same slope. -/
theorem affine_openDisc_of_constant_derivative_rv {a b : K} {r s : O.ValueGroup}
    (hr : r ≠ 0) (hA : (openDisc O a r).Nontrivial) {f d : K → K}
    (hinj : Set.InjOn f (openDisc O a r)) (himage : f '' openDisc O a r = openDisc O b s)
    {u : RV0 O} (hder : ∀ x ∈ openDisc O a r, rv O (d x) = u)
    (hmvt : ∀ x ∈ openDisc O a r, ∀ y ∈ openDisc O a r, x ≠ y →
      ∃ c ∈ openDisc O a r, f x - f y = d c * (x - y)) :
    ∃ t : RV O, (t : RV0 O) = u ∧ RVAffineOn O (openDisc O a r) f t ∧
      s = (unsignedValueUnit O t : O.ValueGroup) * r := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hA
  obtain ⟨c, hc, hsec⟩ := hmvt x hx y hy hxy
  have hdc : d c ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hsec
    exact hxy (hinj hx hy (sub_eq_zero.mp hsec))
  have hu : u ≠ 0 := hder c hc ▸ (rv_eq_zero_iff O).not.mpr hdc
  obtain ⟨t, rfl⟩ := WithZero.ne_zero_iff_exists.mp hu
  have haff := rvAffine_of_mean_value O hder hmvt
  have hk : unsignedValueUnit O t ≠ 0 := (Group.isUnit t).map (unsignedValueUnit O) |>.ne_zero
  exact ⟨t, rfl, haff, radius_eq_shift_mul O hr hk himage
    (haff.toValAffine O)⟩

end GeneralizedEuler.Section3
