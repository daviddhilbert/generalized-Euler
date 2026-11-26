module

public import Section3.AffineSlopes
import all Section3.AffineSlopes

/-! The two translated-fiber descriptions of a balanced two-cell,
including the zero paradigm. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- A positioned family of fibers over a field domain. -/
@[expose] def positionedCell (A : Set K) (f : K → K) (t : RV0 O) : Set (K × K) :=
  {p | p.1 ∈ A ∧ rv O (p.2 - f p.1) = t}

theorem positionedCell_zero (A : Set K) (f : K → K) :
    positionedCell O A f 0 = {p | p.1 ∈ A ∧ p.2 = f p.1} := by
  ext p
  simp only [positionedCell,Set.mem_ofPred_eq,rv_eq_zero_iff,sub_eq_zero]

theorem reverse_positionedCell_zero (A : Set K) (f : K → K) (hinj : Set.InjOn f A)
    {a : K} (ha : a ∈ A) :
    {x ∈ A | (x,f a) ∈ positionedCell O A f 0} = {a} := by
  ext x
  rw [positionedCell_zero]
  constructor
  · rintro ⟨hx,_,he⟩
    exact Set.mem_singleton_iff.2 (hinj hx ha he.symm)
  · intro hx
    obtain rfl : x = a := Set.mem_singleton_iff.1 hx
    exact ⟨ha,ha,rfl⟩

/-- The opposite paradigm is the negative of the original one divided
by the slope. Negation of a leading term is multiplication by rv(-1). -/
@[expose] def oppositeParadigm (t : RV0 O) (u : RV O) : RV0 O :=
  rv O (-1) * (t / (u : RV0 O))

theorem oppositeParadigm_zero (u : RV O) : oppositeParadigm O 0 u = 0 := by
  simp only [oppositeParadigm,zero_div (G₀ := RV0 O),mul_zero (M₀ := RV0 O)]

theorem affine_fiber_iff {A : Set K} {f : K → K} {u : RV O}
    (hF : RVAffineOn O A f u) {x a : K} (hx : x ∈ A) (ha : a ∈ A) (t : RV0 O) :
    rv O (f x - f a) = t ↔ rv O (a - x) = oppositeParadigm O t u := by
  have reverse : rv O (a - x) = rv O (-1) * rv O (x - a) := by
    rw [← neg_sub x a,← neg_one_mul (x - a),map_mul]
  unfold RVAffineOn at hF
  rw [hF x hx a ha,reverse,oppositeParadigm]
  constructor
  · intro h
    have he : rv O (x - a) = t / (u : RV0 O) :=
      (eq_div_iff (G₀ := RV0 O) WithZero.coe_ne_zero).2 (by rwa [mul_comm (G := RV0 O)])
    rw [he]
  · intro h
    have ne : rv O (-1) ≠ 0 := (rv_eq_zero_iff O).not.mpr (neg_ne_zero.mpr one_ne_zero)
    have he := rv_mul_left_cancel O ne h
    rw [mul_comm (G := RV0 O)]
    exact (eq_div_iff (G₀ := RV0 O) WithZero.coe_ne_zero).1 he

theorem unsignedValue_oppositeParadigm (t : RV0 O) (u : RV O) :
    unsignedValue O (oppositeParadigm O t u) = unsignedValue O t / unsignedValueUnit O u := by
  obtain ⟨a,rfl⟩ := rv_surjective O t
  obtain ⟨b,hb⟩ := rv_surjective O (u : RV0 O)
  have hdiv : rv O (a / b) = rv O a / rv O b := by
    rw [div_eq_mul_inv (G := K), map_mul, rv_inv, div_eq_mul_inv (G := RV0 O)]
  rw [oppositeParadigm, ← hb, ← hdiv, ← map_mul (rv O), unsignedValue_rv,
    map_mul O.valuation, O.valuation.map_neg, map_one, one_mul, map_div₀,
    unsignedValue_rv, ← unsignedValue_coe, ← hb, unsignedValue_rv]

/-- The target radius condition of the balanced case supplies the
source radius bound for the opposite paradigm. -/
theorem oppositeParadigm_small_of_target_radius {a b : K} {r s : O.ValueGroup}
    (hr : r ≠ 0) {f : K → K} {u : RV O}
    (hf : RVAffineOn O (openDisc O a r) f u) (image : f '' openDisc O a r = openDisc O b s)
    {t : RV0 O} (small : unsignedValue O t < s) :
    unsignedValue O (oppositeParadigm O t u) < r := by
  have nonzero : unsignedValueUnit O u ≠ 0 := (Group.isUnit u).map (unsignedValueUnit O) |>.ne_zero
  have eq := radius_eq_shift_mul O hr nonzero image (hf.toValAffine O)
  rw [unsignedValue_oppositeParadigm, div_lt_iff₀ (pos_iff_ne_zero.mpr nonzero)]
  simpa only [eq, mul_comm] using small

/-- With the radius inequality in Lemma 5.20, the entire opposite fiber
lies in the open source disc. -/
theorem opposite_fiber_subset_openDisc {a c : K} {r : O.ValueGroup} (ha : a ∈ openDisc O c r)
    {t : RV0 O} {u : RV O}
    (small : unsignedValue O (oppositeParadigm O t u) < r) :
    {x | rv O (a - x) = oppositeParadigm O t u} ⊆ openDisc O c r := by
  intro x hx
  rw [← openDisc_change_center O ha]
  change O.valuation (x - a) < r
  change rv O (a - x) = oppositeParadigm O t u at hx
  have he := congrArg (unsignedValue O) hx
  rw [unsignedValue_rv, ← neg_sub x a, O.valuation.map_neg] at he
  exact he ▸ small

/-- If the target fiber is positioned at `f a`, its preimage is the
opposite fiber in the source disc. -/
theorem affine_preimage_fiber_openDisc {f : K → K} {c a : K} {r : O.ValueGroup} {t : RV0 O}
    {u : RV O} (ha : a ∈ openDisc O c r) (hf : RVAffineOn O (openDisc O c r) f u)
    (small : unsignedValue O (oppositeParadigm O t u) < r) :
    {x ∈ openDisc O c r | rv O (f x - f a) = t} =
      {x | rv O (a - x) = oppositeParadigm O t u} := by
  ext x
  constructor
  · rintro ⟨hx,h⟩
    exact (affine_fiber_iff O hf hx ha t).1 h
  · intro hx
    have h := opposite_fiber_subset_openDisc O ha small hx
    exact ⟨h,(affine_fiber_iff O hf h ha t).2 hx⟩

/-- Translation in the second coordinate makes a positioned cell a
product and fixes the first coordinate. -/
theorem positionedCell_translate (A : Set K) (f : K → K) (t : RV0 O) :
    (fun p : K × K => (p.1,p.2 - f p.1)) '' positionedCell O A f t =
      A ×ˢ (rv O ⁻¹' {t}) := by
  ext p
  constructor
  · rintro ⟨⟨x,y⟩,h,rfl⟩
    exact h
  · rintro ⟨ha,hr⟩
    refine ⟨(p.1,p.2 + f p.1),⟨ha,?_⟩,Prod.ext rfl (add_sub_cancel_right _ _)⟩
    change rv O (p.2 + f p.1 - f p.1) = t
    rwa [add_sub_cancel_right]

/-- For a balanced cell the other coordinate likewise translates to a
fixed leading-term fiber. On the nonzero branch the source radius
assumption guarantees that this whole fiber is present. -/
theorem positionedCell_translate_first {c : K} {r : O.ValueGroup} {f g : K → K}
    {t : RV0 O} {u : RV O} (B : Set K)
    (hf : RVAffineOn O (openDisc O c r) f u)
    (small : unsignedValue O (oppositeParadigm O t u) < r)
    (target : ∀ p ∈ positionedCell O (openDisc O c r) f t, p.2 ∈ B)
    (inverse : ∀ b ∈ B, g b ∈ openDisc O c r ∧ f (g b) = b) :
    (fun p : K × K => (p.1 - g p.2,p.2)) '' positionedCell O (openDisc O c r) f t =
      (rv O ⁻¹' {oppositeParadigm O t u}) ×ˢ B := by
  ext p
  constructor
  · rintro ⟨a,ha,rfl⟩
    have hb := target a ha
    obtain ⟨hg,hfg⟩ := inverse a.2 hb
    refine ⟨?_,hb⟩
    apply (affine_fiber_iff O hf hg ha.1 t).1
    rw [hfg]
    exact ha.2
  · rintro ⟨ht,hb⟩
    obtain ⟨hg,hfg⟩ := inverse p.2 hb
    let x := p.1 + g p.2
    have hx : x ∈ openDisc O c r := by
      rw [← openDisc_change_center O hg]
      change O.valuation (p.1 + g p.2 - g p.2) < r
      rw [add_sub_cancel_right, ← unsignedValue_rv]
      change rv O p.1 = oppositeParadigm O t u at ht
      rwa [ht]
    have ht' : rv O (x - g p.2) = oppositeParadigm O t u := by
      change rv O (p.1 + g p.2 - g p.2) = _
      rwa [add_sub_cancel_right]
    have he := (affine_fiber_iff O hf hg hx t).2 ht'
    rw [hfg] at he
    exact ⟨(x,p.2),⟨hx,he⟩,Prod.ext (add_sub_cancel_right _ _) rfl⟩

end GeneralizedEuler.Section5
