module

public import Section2.HollyNormalForm

/-! Defining the end discs from the rays of a nonempty valuative interval. -/

public section

namespace GeneralizedEuler.Section2

section OrderedGroup

variable {A : Type*} [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]

/-- Translation by this difference preserves membership in the ray. -/
@[expose]
def rayPeriod (U : Set A) (d : A) : Prop := ∀ x, x ∈ U ↔ x + d ∈ U

/-- The lowest translation class in an upward ray, if it has one. -/
@[expose]
def lowerEndClass (U : Set A) : Set A :=
  {x | x ∈ U ∧ ∀ y ∈ U, x ≤ y ∨ rayPeriod U (x - y)}

private theorem rayPeriod_upperCoset {H : AddSubgroup A} (hH : (H : Set A).OrdConnected)
    (c : A) (d : A) :
    rayPeriod {x | ∃ z, z - c ∈ H ∧ z ≤ x} d ↔ d ∈ H := by
  let U : Set A := {x | ∃ z, z - c ∈ H ∧ z ≤ x}
  have hc : c ∈ U := ⟨c, by simp, le_rfl⟩
  have hb (x : A) (hx : x ≤ c) (h : x ∈ U) : x - c ∈ H := by
    obtain ⟨z, hz, hzx⟩ := h
    exact hH.out hz H.zero_mem ⟨sub_le_sub_right hzx c, sub_nonpos.mpr hx⟩
  change (∀ x, x ∈ U ↔ x + d ∈ U) ↔ d ∈ H
  constructor
  · intro h
    rcases le_total d 0 with hd | hd
    · have hm := hb (c + d) (by simpa using hd) ((h c).mp hc)
      simpa [add_sub_cancel_left] using hm
    · have hu : c - d ∈ U := (h (c - d)).mpr (by simpa using hc)
      have hm := H.neg_mem (hb (c - d) (by simpa using hd) hu)
      simpa [sub_right_comm] using hm
  · intro hd x
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z + d, by rw [add_sub_right_comm]; exact H.add_mem hz hd,
        add_le_add_left hzx d⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z - d, by rw [sub_right_comm]; exact H.sub_mem hz hd,
        sub_le_iff_le_add.mpr hzx⟩

private theorem lowerEndClass_upperCoset {H : AddSubgroup A}
    (hH : (H : Set A).OrdConnected) (c : A) :
    lowerEndClass {x | ∃ z, z - c ∈ H ∧ z ≤ x} = {x | x - c ∈ H} := by
  let U : Set A := {x | ∃ z, z - c ∈ H ∧ z ≤ x}
  change lowerEndClass U = _
  ext x
  change (x ∈ U ∧ ∀ y ∈ U, x ≤ y ∨ rayPeriod U (x - y)) ↔ x - c ∈ H
  simp only [show ∀ d, rayPeriod U d ↔ d ∈ H from rayPeriod_upperCoset hH c]
  constructor
  · rintro ⟨⟨z, hz, hzx⟩, hx⟩
    have hzero := H.zero_mem
    rcases hx c ⟨c, by simp, le_rfl⟩ with hxc | hx
    · exact hH.out hz hzero ⟨sub_le_sub_right hzx c, sub_nonpos.mpr hxc⟩
    · exact hx
  · intro hx
    refine ⟨⟨x, hx, le_rfl⟩, ?_⟩
    intro y hy
    by_cases hxy : x ≤ y
    · exact .inl hxy
    · obtain ⟨z, hz, hzy⟩ := hy
      have hm : y - c ∈ H :=
        hH.out hz hx ⟨sub_le_sub_right hzy c, sub_le_sub_right (le_of_not_ge hxy) c⟩
      exact .inr (by simpa using H.sub_mem hx hm)

end OrderedGroup

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO

theorem IsEndDisc.exists_convexAddSubgroup {D : Set K} (hD : IsEndDisc O D) :
    ∃ (c : K) (H : AddSubgroup K), (H : Set K).OrdConnected ∧ D = {x | x - c ∈ H} := by
  rcases hD with ⟨c, rfl⟩ | ⟨c, r, hr, rfl | rfl⟩
  · refine ⟨c, ⊥, ?_, ?_⟩
    · simpa using (Set.ordConnected_singleton (a := (0 : K)))
    · ext x
      simp [sub_eq_zero]
  · let H : AddSubgroup K :=
      { carrier := {x | O.valuation x < r}
        zero_mem' := by simpa using (pos_iff_ne_zero.mpr hr)
        add_mem' := fun hx hy => (O.valuation.map_add _ _).trans_lt (max_lt hx hy)
        neg_mem' := fun hx => by simpa only [Set.mem_ofPred_eq, O.valuation.map_neg] using hx }
    refine ⟨c, H, ?_, rfl⟩
    simpa [H, Set.Iio, sub_zero] using
      (valuativeDisc_ordConnected O hO (0 : K) (Set.Iio r) (fun _ _ hab hb => hab.trans_lt hb))
  · let H : AddSubgroup K :=
      { carrier := {x | O.valuation x ≤ r}
        zero_mem' := by simp
        add_mem' := fun hx hy => (O.valuation.map_add _ _).trans (max_le hx hy)
        neg_mem' := fun hx => by simpa only [Set.mem_ofPred_eq, O.valuation.map_neg] using hx }
    refine ⟨c, H, ?_, rfl⟩
    simpa [H, Set.Iic, sub_zero] using
      (valuativeDisc_ordConnected O hO (0 : K) (Set.Iic r) (fun _ _ hab hb => hab.trans hb))

theorem IsEndDisc.eq_lowerEndClass_upperRay {D : Set K} (hD : IsEndDisc O D) :
    lowerEndClass {x | ∃ z ∈ D, z ≤ x} = D := by
  obtain ⟨c, H, hH, rfl⟩ := hD.exists_convexAddSubgroup O hO
  exact lowerEndClass_upperCoset hH c

theorem IsEndDisc.eq_lowerEndClass_lowerRay {D : Set K} (hD : IsEndDisc O D) :
    lowerEndClass (A := Kᵒᵈ) {x | ∃ z ∈ D, (show K from x) ≤ z} = D := by
  obtain ⟨c, H, hH, rfl⟩ := hD.exists_convexAddSubgroup O hO
  exact lowerEndClass_upperCoset (A := Kᵒᵈ) hH.dual c

end GeneralizedEuler.Section2
