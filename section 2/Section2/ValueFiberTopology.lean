module

public import Section2.Dimension
public import Section2.LeadingTermOrder

/-! A nonzero unsigned value has an open fiber in the signed RV order. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rv_neg (x : K) : rv O (-x) = rv O (-1) * rv O x := by
  rw [← map_mul (rv O), neg_one_mul]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem rv_neg_eq_iff (x y : K) : rv O (-x) = rv O (-y) ↔ rv O x = rv O y := by
  have hn : rv O (-1) ≠ 0 := (rv_eq_zero_iff O).not.mpr (neg_ne_zero.mpr one_ne_zero)
  rw [rv_neg O x, rv_neg O y]
  exact ⟨rv_mul_left_cancel O hn, congrArg (fun t : RV0 O => rv O (-1) * t)⟩

private theorem value_two (hO : IsOrderConvex O) : O.valuation (2 : K) = 1 := by
  have h1 : O.valuation (1 : K) ≤ O.valuation (2 : K) :=
    valuation_le_of_nonneg_le O hO zero_le_one one_le_two
  have h2 : (2 : K) ∈ O := by
    rw [← one_add_one_eq_two]
    exact O.add_mem 1 1 O.one_mem O.one_mem
  exact ((O.valuation_le_one_iff 2).mpr h2).antisymm (by simpa only [map_one] using h1)

private theorem positive_bounds (hO : IsOrderConvex O) {x : K} (hx : 0 < x) :
    ∃ b c : K, b < x ∧ x < c ∧ rv O b ≠ rv O x ∧ rv O x ≠ rv O c ∧
      ∀ y, b < y → y < c → O.valuation y = O.valuation x := by
  let b := x / 2
  let c := x + x
  have hb : 0 < b := div_pos hx zero_lt_two
  have hc : 0 < c := add_pos hx hx
  have hbval : O.valuation b = O.valuation x := by
    change O.valuation (x / 2) = _
    rw [map_div₀, value_two O hO, div_one]
  have hcval : O.valuation c = O.valuation x := by
    change O.valuation (x + x) = _
    rw [← two_mul, map_mul, value_two O hO, one_mul]
  refine ⟨b, c, div_lt_self hx one_lt_two, lt_add_of_pos_right x hx, ?_, ?_, ?_⟩
  · intro heq
    have h := (rv_eq_rv_iff_valuation O hb.ne').mp heq.symm
    change O.valuation (x - x / 2) < O.valuation (x / 2) at h
    rw [sub_half] at h
    exact (lt_irrefl _) h
  · intro heq
    have h := (rv_eq_rv_iff_valuation O hx.ne').mp heq.symm
    change O.valuation (x + x - x) < O.valuation x at h
    rw [add_sub_cancel_right] at h
    exact (lt_irrefl _) h
  · intro y hby hyc
    have hleft := valuation_le_of_nonneg_le O hO hb.le hby.le
    have hright := valuation_le_of_nonneg_le O hO (hb.le.trans hby.le) hyc.le
    rw [hbval] at hleft
    rw [hcval] at hright
    exact hright.antisymm hleft

private theorem bounds (hO : IsOrderConvex O) {x : K} (hx : x ≠ 0) :
    ∃ b c : K, b < x ∧ x < c ∧ rv O b ≠ rv O x ∧ rv O x ≠ rv O c ∧
      ∀ y, b < y → y < c → O.valuation y = O.valuation x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · obtain ⟨b, c, hb, hc, hbrv, hcrv, hval⟩ := positive_bounds O hO (neg_pos.mpr hn)
    refine ⟨-c, -b, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [neg_neg] using neg_lt_neg hc
    · simpa only [neg_neg] using neg_lt_neg hb
    · rw [← neg_neg x, ne_eq, rv_neg_eq_iff]
      exact hcrv.symm
    · rw [← neg_neg x, ne_eq, rv_neg_eq_iff]
      exact hbrv.symm
    · intro y hcy hyb
      have hy₁ : b < -y := by simpa only [neg_neg] using neg_lt_neg hyb
      have hy₂ : -y < c := by simpa only [neg_neg] using neg_lt_neg hcy
      simpa only [O.valuation.map_neg] using hval (-y) hy₁ hy₂
  · exact positive_bounds O hO hp

/-- The order topology of the signed RV order. -/
@[expose, instance_reducible]
def rvOrderTopology (hO : IsOrderConvex O) : TopologicalSpace (RV0 O) :=
  letI := rvLinearOrder O hO
  Preorder.topology _

set_option linter.style.haveILetI false in
/-- In the signed RV order any fiber of a nonzero unsigned value is open.
The fiber over value zero consists of the separate RV zero. -/
theorem unsignedValue_fiber_isOpen (hO : IsOrderConvex O) {γ : O.ValueGroup} (hγ : γ ≠ 0) :
    letI := rvOrderTopology O hO
    IsOpen (unsignedValue O ⁻¹' {γ}) := by
  letI := rvLinearOrder O hO
  letI := rvOrderTopology O hO
  letI : OrderTopology (RV0 O) := ⟨rfl⟩
  apply isOpen_iff_forall_mem_open.mpr
  intro t ht
  obtain ⟨x, rfl⟩ := rv_surjective O t
  have hxval : O.valuation x = γ := (unsignedValue_rv O x).symm.trans ht
  have hx : x ≠ 0 := by
    intro he
    rw [he, map_zero] at hxval
    exact hγ hxval.symm
  obtain ⟨b, c, hb, hc, hbrv, hcrv, hval⟩ := bounds O hO hx
  refine ⟨Set.Ioo (rv O b) (rv O c), ?_, isOpen_Ioo,
    ⟨(rv_lt_rv_iff O hO).mpr ⟨hb, hbrv⟩, (rv_lt_rv_iff O hO).mpr ⟨hc, hcrv⟩⟩⟩
  intro s hs
  obtain ⟨y, rfl⟩ := rv_surjective O s
  have hy₁ := ((rv_lt_rv_iff O hO).mp hs.1).1
  have hy₂ := ((rv_lt_rv_iff O hO).mp hs.2).1
  exact (unsignedValue_rv O y).trans ((hval y hy₁ hy₂).trans hxval)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem unsignedValue_eq_zero_iff (t : RV0 O) :
    unsignedValue O t = 0 ↔ t = 0 := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  rw [unsignedValue_rv, rv_eq_zero_iff, map_eq_zero]

/-- A signed value, coded by its negative sign and its unsigned value.
Only the value of RV zero has unsigned component zero. -/
def signedValueLabel (hO : IsOrderConvex O) (t : RV0 O) : Bool × O.ValueGroup :=
  letI := rvLinearOrder O hO
  (decide (t < 0), unsignedValue O t)

set_option linter.style.haveILetI false in
theorem signedValue_fiber_isOpen (hO : IsOrderConvex O) {t : RV0 O} (ht : t ≠ 0) :
    letI := rvOrderTopology O hO
    IsOpen (signedValueLabel O hO ⁻¹' {signedValueLabel O hO t}) := by
  letI := rvLinearOrder O hO
  letI := rvOrderTopology O hO
  letI : OrderTopology (RV0 O) := ⟨rfl⟩
  have hγ : unsignedValue O t ≠ 0 := (unsignedValue_eq_zero_iff O t).not.mpr ht
  have hV := unsignedValue_fiber_isOpen O hO hγ
  by_cases hs : t < 0
  · have heq : signedValueLabel O hO ⁻¹' {signedValueLabel O hO t} =
        Set.Iio 0 ∩ unsignedValue O ⁻¹' {unsignedValue O t} := by
      ext s
      simp only [Set.mem_preimage, Set.mem_singleton_iff, signedValueLabel,
        Prod.mk.injEq, Set.mem_inter_iff, Set.mem_Iio, decide_eq_true hs, decide_eq_true_eq]
    rw [heq]
    exact isOpen_Iio.inter hV
  · have heq : signedValueLabel O hO ⁻¹' {signedValueLabel O hO t} =
        Set.Ioi 0 ∩ unsignedValue O ⁻¹' {unsignedValue O t} := by
      ext s
      simp only [Set.mem_preimage, Set.mem_singleton_iff, signedValueLabel,
        Prod.mk.injEq, Set.mem_inter_iff, Set.mem_Ioi, decide_eq_false hs, decide_eq_false_iff_not]
      refine and_congr_left fun hval => ⟨fun hn => ?_, fun hp => hp.not_gt⟩
      have hne : s ≠ 0 := (unsignedValue_eq_zero_iff O s).not.mp (hval.trans_ne hγ)
      exact lt_of_le_of_ne (not_lt.mp hn) hne.symm
    rw [heq]
    exact isOpen_Ioi.inter hV

set_option linter.style.haveILetI false in
theorem signedValue_tuple_fiber_isOpen (hO : IsOrderConvex O) {n : ℕ}
    {x : Fin n → RV0 O} (hx : ∀ i, x i ≠ 0) :
    letI := rvOrderTopology O hO
    IsOpen ((fun y : Fin n → RV0 O => signedValueLabel O hO ∘ y) ⁻¹'
      {signedValueLabel O hO ∘ x}) := by
  letI := rvOrderTopology O hO
  let sets : Fin n → Set (Fin n → RV0 O) :=
    fun i => (fun y => y i) ⁻¹' (signedValueLabel O hO ⁻¹' {signedValueLabel O hO (x i)})
  have heq : (fun y : Fin n → RV0 O => signedValueLabel O hO ∘ y) ⁻¹'
      {signedValueLabel O hO ∘ x} = ⋂ i, sets i := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Function.comp_apply,
      Set.mem_iInter, sets]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => (signedValue_fiber_isOpen O hO (hx i)).preimage
    (continuous_apply i))

set_option linter.style.haveILetI false in
/-- The dimension conclusion of Lemma 2.28 from a maximal-dimensional
coordinate chart supplied by weakly o-minimal cell decomposition. -/
theorem signedValue_fiber_dimension (hO : IsOrderConvex O) {n : ℕ}
    (D : Set (Fin n → RV0 O)) (hnonzero : ∀ x ∈ D, ∀ i, x i ≠ 0)
    (k : ℕ) (e : Fin k ↪ Fin n) (U : Set (Fin k → RV0 O))
    (chart : (Fin k → RV0 O) → (Fin n → RV0 O))
    (hne : U.Nonempty) (hchart : Set.MapsTo chart U D)
    (hproj : ∀ u ∈ U, coordinateProjection e (chart u) = u)
    (htop : letI := rvOrderTopology O hO
            IsOpen U ∧ ContinuousOn chart U ∧ projectionDimension D = k) :
    letI := rvOrderTopology O hO
    ∃ x ∈ D, projectionDimension (D ∩
      (fun y : Fin n → RV0 O => signedValueLabel O hO ∘ y) ⁻¹'
        {signedValueLabel O hO ∘ x}) = k := by
  letI := rvOrderTopology O hO
  obtain ⟨hU, hc, hk⟩ := htop
  obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := fiber_hasInteriorProjection_of_chart D
    (fun y => signedValueLabel O hO ∘ y)
    (fun y hy => signedValue_tuple_fiber_isOpen O hO (hnonzero y hy))
    e U hU hne chart hc hchart hproj
  exact ⟨x, hx, (le_projectionDimension h).antisymm'
    ((projectionDimension_mono Set.inter_subset_left).trans_eq hk)⟩

end GeneralizedEuler.Section2
