module

public import Section2.LeadingTermOrder
public import Section2.LeadingTermPower
public import Section2.Residue

/-! Ordered and residue-compatible RV powers, as required by Ax. 10. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

/-- An increasing field power with a descended left inverse is strictly
increasing on the positive RV branch. For a positive exponent the left
inverse is the power with reciprocal exponent. -/
theorem leadingTermPower_strictMonoOn (hO : IsOrderConvex O)
    {g gInv : PositiveField K →* PositiveField K} {P PInv : RV0 O → RV0 O}
    (hP : AgreesWithFieldPower O g P) (hInv : AgreesWithFieldPower O gInv PInv)
    (hg : StrictMono g) (hleft : Function.LeftInverse gInv g) :
    letI := rvLinearOrder O hO
    StrictMonoOn P {t | IsPositiveRV O t} := by
  intro s hs t ht hst
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  have hxy := ((rv_lt_rv_iff O hO).mp hst).1
  rw [hP, hP]
  apply (rv_lt_rv_iff O hO).mpr
  refine ⟨hg hxy, ?_⟩
  intro hEq
  have h := congrArg PInv hEq
  rw [hInv, hInv, hleft x, hleft y] at h
  exact ((rv_lt_rv_iff O hO).mp hst).2 h

/-- A positive field power that sends positive integral elements into the
ring also sends positive valuation units to valuation units. -/
theorem positive_power_preserves_units (g : PositiveField K →* PositiveField K)
    (hg : ∀ x : PositiveField K, (x : K) ∈ O → (g x : K) ∈ O)
    (x : PositiveField K) (hx : O.valuation (x : K) = 1) :
    O.valuation (g x : K) = 1 := by
  have hxO : (x : K) ∈ O := (O.valuation_le_one_iff _).mp hx.le
  have hxInv : ((x⁻¹ : PositiveField K) : K) ∈ O := by
    rw [← O.valuation_le_one_iff, Positive.coe_inv, map_inv₀, hx, inv_one]
  have hInv := hg x⁻¹ hxInv
  rw [map_inv, Positive.coe_inv, ← O.valuation_le_one_iff, map_inv₀] at hInv
  have hnonzero := (map_ne_zero O.valuation).mpr (g x).property.ne'
  exact ((O.valuation_le_one_iff _).mpr (hg x hxO)).antisymm
    ((inv_le_one₀ (pos_iff_ne_zero.mpr hnonzero)).mp hInv)

/-- A field power preserving positive valuation units acts on the unsigned
values of all positive elements. -/
theorem power_respects_unsignedValue (g : PositiveField K →* PositiveField K)
    (hunit : ∀ x : PositiveField K, O.valuation (x : K) = 1 →
      O.valuation (g x : K) = 1)
    {x y : PositiveField K} (hxy : O.valuation (x : K) = O.valuation (y : K)) :
    O.valuation (g x : K) = O.valuation (g y : K) := by
  have coe_div (a b : PositiveField K) :
      ((a / b : PositiveField K) : K) = (a : K) / (b : K) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rfl
  have hy : O.valuation (y : K) ≠ 0 := (map_ne_zero O.valuation).mpr y.property.ne'
  have hquot : O.valuation ((x / y : PositiveField K) : K) = 1 := by
    rw [coe_div, map_div₀, hxy, div_self hy]
  have h := hunit (x / y) hquot
  have hgy : O.valuation (g y : K) ≠ 0 :=
    (map_ne_zero O.valuation).mpr (g y).property.ne'
  rw [map_div, coe_div, map_div₀] at h
  exact (div_eq_one_iff_eq hgy).mp h

/-- Agreement on positive residue elements follows by reducing a positive
unit whenever the total positive-branch extension of the field power
commutes with reduction. -/
theorem leadingTermPower_residue (g : PositiveField K →* PositiveField K)
    (P : RV0 O → RV0 O) (hP : AgreesWithFieldPower O g P) (gRes : Residue O → Residue O)
    (hmatch : ResidueCompatible O (fun x => if h : 0 < x then (g ⟨x, h⟩ : K) else 0) gRes)
    (x : PositiveField K) (hxO : (x : K) ∈ O)
    (hx : IsLocalRing.residue O (⟨x, hxO⟩ : O) ≠ 0)
    (hout : gRes (IsLocalRing.residue O (⟨x, hxO⟩ : O)) ≠ 0) :
    P (residueRV O (IsLocalRing.residue O (⟨x, hxO⟩ : O))) =
      residueRV O (gRes (IsLocalRing.residue O (⟨x, hxO⟩ : O))) := by
  let y : O := ⟨x, hxO⟩
  have hmatch' : ∃ h : (g x : K) ∈ O,
      IsLocalRing.residue O (⟨g x, h⟩ : O) = gRes (IsLocalRing.residue O y) := by
    change ∀ a : O, ∃ h : (if hp : 0 < (a : K) then (g ⟨a, hp⟩ : K) else 0) ∈ O,
      IsLocalRing.residue O ⟨_, h⟩ = gRes (IsLocalRing.residue O a) at hmatch
    have hy : 0 < (y : K) := x.property
    simpa only [dite_eq_left hy] using hmatch y
  obtain ⟨hgO, hgRes⟩ := hmatch'
  rw [residueRV_residue_of_ne_zero O y hx, hP, ← hgRes,
    residueRV_residue_of_ne_zero O (⟨g x, hgO⟩ : O) (hgRes.trans_ne hout)]

end GeneralizedEuler.Section2
