module

public import Section5.CenteredDiscContraction
public import Section5.BalancedCells

/-! Lemma 5.16 before unary preparation. The distance label is constant
on the inverse image of each positioned fiber. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem positioned_fiber_is_openDisc {a : K} {t : RV0 O} (ht : t ≠ 0) :
    ∃ c r, r ≠ 0 ∧ {b | rv O (b-a) = t} = openDisc O c r := by
  obtain ⟨z,rfl⟩ := rv_surjective O t
  have hn : z ≠ 0 := (rv_eq_zero_iff O).not.1 ht
  refine ⟨a+z,O.valuation z,(map_ne_zero O.valuation).2 hn,?_⟩
  ext b
  change rv O (b-a) = rv O z ↔ O.valuation (b-(a+z)) < O.valuation z
  rw [rv_eq_rv_iff_valuation O hn,sub_sub]

/-- For a zero label the inverse fiber is a singleton. With a nonzero
label disc-to-disc makes it an open disc avoiding the original point. -/
theorem positioning_distance_constant {A B : Set K} {f g : K → K}
    (dtdp : DiscToDiscOn O A B f g)
    {a : K} (ha : a ∈ A) (t : RV0 O)
    (sub : {b | rv O (b-f a) = t} ⊆ B)
    {x y : K} (hx : x ∈ A) (hy : y ∈ A)
    (xLabel : rv O (f x - f a) = t) (yLabel : rv O (f y - f a) = t) :
    rv O (a-x) = rv O (a-y) := by
  by_cases h0 : t = 0
  · have hxe : x = a := dtdp.1.injOn hx ha (sub_eq_zero.1 ((rv_eq_zero_iff O).1 (xLabel.trans h0)))
    have hye : y = a := dtdp.1.injOn hy ha (sub_eq_zero.1 ((rv_eq_zero_iff O).1 (yLabel.trans h0)))
    rw [hxe,hye]
  · obtain ⟨c,r,hr,fiber⟩ := positioned_fiber_is_openDisc O (a := f a) h0
    obtain ⟨c',r',hr',invFiber⟩ := dtdp.2.2.2 c r hr (fiber ▸ sub)
    have invX : x ∈ openDisc O c' r' := by
      rw [← invFiber,← fiber]
      exact ⟨f x,xLabel,dtdp.2.1.1 hx⟩
    have invY : y ∈ openDisc O c' r' := by
      rw [← invFiber,← fiber]
      exact ⟨f y,yLabel,dtdp.2.1.1 hy⟩
    have outside : a ∉ openDisc O c' r' := by
      rw [← invFiber,← fiber]
      rintro ⟨b,hb,eq⟩
      have bEq : b = f a := (dtdp.2.1.2 (sub hb)).symm.trans (congrArg f eq)
      change rv O (b-f a) = t at hb
      rw [bEq,sub_self,map_zero] at hb
      exact h0 hb.symm
    have he := rv_sub_const_of_openDisc_avoids O hr' outside invX invY
    rw [← neg_sub x a,← neg_sub y a,← neg_one_mul (x-a),← neg_one_mul (y-a),map_mul,map_mul,he]

/-- If the positioning image lies in a disc of radius at most the
paradigm's value, every positioned fiber is the same fiber. -/
theorem positionedCell_product_of_radius {A : Set K} {f : K → K} {a c : K}
    {r : O.ValueGroup} (hr : r ≠ 0) (ha : a ∈ A)
    (contain : Set.MapsTo f A (openDisc O c r))
    {t : RV0 O} (large : r ≤ unsignedValue O t) :
    positionedCell O A f t = A ×ˢ {z | rv O (z - f a) = t} := by
  have anchor (x : K) (hx : x ∈ A) (y : K) (h : rv O (y - f x) = t) :
      rv O (y - f a) = rv O (y - f x) := by
    have outside : y ∉ openDisc O c r := by
      intro hy
      rw [← openDisc_change_center O (contain hx)] at hy
      change O.valuation (y-f x) < r at hy
      have val := congrArg (unsignedValue O) h
      rw [unsignedValue_rv] at val
      exact (val ▸ hy).not_ge large
    have labels := rv_sub_const_of_openDisc_avoids O hr outside (contain ha) (contain hx)
    rw [← neg_sub (f a) y,← neg_sub (f x) y,← neg_one_mul (f a-y),← neg_one_mul (f x-y),
      map_mul,map_mul,labels]
  ext p
  constructor
  · intro hp
    exact ⟨hp.1,(anchor p.1 hp.1 p.2 hp.2).trans hp.2⟩
  · intro hp
    have outside : p.2 ∉ openDisc O c r := by
      intro hy
      rw [← openDisc_change_center O (contain ha)] at hy
      change O.valuation (p.2-f a) < r at hy
      have hv : rv O (p.2-f a) = t := hp.2
      have val := congrArg (unsignedValue O) hv
      rw [unsignedValue_rv] at val
      exact (val ▸ hy).not_ge large
    have labels := rv_sub_const_of_openDisc_avoids O hr outside (contain hp.1) (contain ha)
    refine ⟨hp.1,?_⟩
    change rv O (p.2 - f p.1) = t
    rw [← neg_sub (f p.1) p.2,← neg_one_mul (f p.1-p.2),map_mul,labels,
      ← map_mul,neg_one_mul,neg_sub]
    exact hp.2

end GeneralizedEuler.Section5
