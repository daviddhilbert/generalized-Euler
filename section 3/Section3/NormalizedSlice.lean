module

public import Section3.ResidueDerivatives
public import Section2.ValuativeDisc

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

/-- The unary test in 3.31 on an interval of constant output value.
G is a total extension of the residue contraction on this interval.
The derivative condition is imposed on every lift of the label r. -/
def NormalizedSliceAt (A : Set O) (g d : O → K) (c : K) (r : Residue O) : Prop :=
  letI := residueLinearOrder O hO
  ∃ G : Residue O → Residue O,
    (∀ x ∈ A, ∃ v : O, (v : K) = g x / c ∧ IsLocalRing.residue O v = G (IsLocalRing.residue O x)) ∧
    ∀ x ∈ A, IsLocalRing.residue O x = r →
      ∃ v : O, (v : K) = d x / c ∧ HasOrderDerivativeAt G r (IsLocalRing.residue O v)

private theorem change_scale {A : Set O} {g d : O → K} {a b : K} {r : Residue O}
    (ha : a ≠ 0) (he : O.valuation a = O.valuation b)
    (ok : NormalizedSliceAt O hO A g d a r) : NormalizedSliceAt O hO A g d b r := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  have hv : O.valuation (a/b) = 1 := by
    rw [map_div₀,←he,div_self ((map_ne_zero _).mpr ha)]
  have hm := (O.valuation_le_one_iff _).mp hv.le
  let u : O := ⟨a/b,hm⟩
  have hu : IsLocalRing.residue O u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr
    ((O.valuation_eq_one_iff u).mpr hv)
  have rescale {w : K} (v : O) (hv : (v : K) = w/a) : ((u*v : O) : K) = w/b := by
    change a/b * (v : K) = w/b
    rw [hv]
    field_simp [ha]
  obtain ⟨G,hG,hD⟩ := ok
  refine ⟨fun s => IsLocalRing.residue O u * G s,?_,?_⟩
  · intro x hx
    obtain ⟨v,hv,hd⟩ := hG x hx
    exact ⟨u*v,rescale v hv,by rw [map_mul,hd]⟩
  · intro x hx hxr
    obtain ⟨v,hv,hder⟩ := hD x hx hxr
    refine ⟨u*v,rescale v hv,?_⟩
    simpa using hder.affine_change 1 (IsLocalRing.residue O u) 0 0 one_ne_zero hu

/-- Any nonzero representative of the same output value gives the same
test result, with no field section of the value map. -/
theorem normalizedSliceAt_iff_of_same_value {A : Set O} {g d : O → K} {a b : K} {r : Residue O}
    (ha : a ≠ 0) (he : O.valuation a = O.valuation b) :
    NormalizedSliceAt O hO A g d a r ↔ NormalizedSliceAt O hO A g d b r :=
  ⟨change_scale O hO ha he, change_scale O hO
    ((map_ne_zero _).mp (he.symm.trans_ne ((map_ne_zero _).mpr ha))) he.symm⟩

end GeneralizedEuler.Section3
