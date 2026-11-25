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

end GeneralizedEuler.Section3
