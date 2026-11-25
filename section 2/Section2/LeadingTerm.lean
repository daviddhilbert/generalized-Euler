module

public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-! The leading-term quotient, with the zero of the field adjoined separately. -/

noncomputable section

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- Quotient the nonzero field elements by a subgroup and adjoin zero. -/
def unitQuotientWithZero (H : Subgroup Kˣ) : K →*₀ WithZero (Kˣ ⧸ H) := by
  classical
  exact (WithZero.map' (QuotientGroup.mk' H)).comp
    (WithZero.withZeroUnitsEquiv (G := K)).symm.toMonoidWithZeroHom

@[simp]
theorem unitQuotientWithZero_coe_unit (H : Subgroup Kˣ) (x : Kˣ) :
    unitQuotientWithZero H (x : K) = (QuotientGroup.mk' H x : WithZero (Kˣ ⧸ H)) := by
  simp [unitQuotientWithZero]

theorem unitQuotientWithZero_eq_zero_iff (H : Subgroup Kˣ) {x : K} :
    unitQuotientWithZero H x = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    intro hx
    let u := Units.mk0 x hx
    change unitQuotientWithZero H (u : K) ≠ 0
    rw [unitQuotientWithZero_coe_unit]
    exact WithZero.coe_ne_zero
  · rintro rfl
    exact map_zero _

theorem unitQuotientWithZero_surjective (H : Subgroup Kˣ) :
    Function.Surjective (unitQuotientWithZero H) := by
  intro t
  cases t using WithZero.recZeroCoe with
  | zero => exact ⟨0, map_zero _⟩
  | coe t =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H t
    exact ⟨x, unitQuotientWithZero_coe_unit H x⟩

/-- The nonzero leading terms are the units modulo the principal units. -/
abbrev RV := Kˣ ⧸ O.principalUnitGroup

/-- The RV sort of the language of §2.2. -/
abbrev RV0 := WithZero (RV O)

/-- The quotient on nonzero field elements. -/
abbrev rvUnit : Kˣ →* RV O := QuotientGroup.mk' O.principalUnitGroup

/-- The canonical leading-term map on the whole field. -/
def rv : K →*₀ RV0 O := unitQuotientWithZero O.principalUnitGroup

@[simp] theorem rv_coe_unit (x : Kˣ) : rv O (x : K) = (rvUnit O x : RV0 O) :=
  unitQuotientWithZero_coe_unit O.principalUnitGroup x

@[simp] theorem rv_eq_zero_iff {x : K} : rv O x = 0 ↔ x = 0 :=
  unitQuotientWithZero_eq_zero_iff O.principalUnitGroup

@[simp] theorem rv_inv (x : K) : rv O x⁻¹ = (rv O x)⁻¹ :=
  map_inv₀ (rv O) x

theorem rv_mul_left_cancel {x y z : RV0 O} (hx : x ≠ 0) (h : x * y = x * z) :
    y = z := by
  have cancel (t : RV0 O) : x⁻¹ * (x * t) = t :=
    inv_mul_cancel_left₀ (G₀ := RV0 O) hx t
  exact (cancel y).symm.trans ((congrArg (fun t : RV0 O => x⁻¹ * t) h).trans (cancel z))

theorem rv_surjective : Function.Surjective (rv O) :=
  unitQuotientWithZero_surjective O.principalUnitGroup

/-- Equality of leading terms is expressible in the valued-field language
by a single maximal-ideal test when the reference term is nonzero. -/
theorem rv_eq_rv_iff {x y : K} (hy : y ≠ 0) :
    rv O x = rv O y ↔ (x - y) / y ∈ O.nonunits := by
  by_cases hx : x = 0
  · subst x
    have h : (-y) / y = -1 := by rw [neg_div, div_self hy]
    rw [zero_sub, h, map_zero, eq_comm, rv_eq_zero_iff, O.mem_nonunits_iff,
      O.valuation.map_neg, map_one]
    simp [hy]
  let u := Units.mk0 x hx
  let v := Units.mk0 y hy
  change rv O (u : K) = rv O (v : K) ↔ ((u : K) - (v : K)) / (v : K) ∈ O.nonunits
  rw [rv_coe_unit, rv_coe_unit, WithZero.coe_inj]
  have hquot : rvUnit O u = rvUnit O v ↔ u / v ∈ O.principalUnitGroup := by
    calc
      rvUnit O u = rvUnit O v ↔ rvUnit O u / rvUnit O v = 1 := div_eq_one.symm
      _ ↔ rvUnit O (u / v) = 1 := by rw [map_div]
      _ ↔ u / v ∈ O.principalUnitGroup := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  rw [hquot, O.mem_principalUnitGroup_iff, O.mem_nonunits_iff]
  rw [Units.val_div_eq_div_val, sub_div, div_self v.ne_zero]

/-- Every nonzero RV fiber is the open disc about any representative
with radius its unsigned value. -/
theorem rv_eq_rv_iff_valuation {x y : K} (hy : y ≠ 0) :
    rv O x = rv O y ↔ O.valuation (x - y) < O.valuation y := by
  rw [rv_eq_rv_iff O hy, O.mem_nonunits_iff, map_div₀]
  exact div_lt_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero O.valuation).mpr hy))

/-- The maximal-ideal predicate can itself be expressed using valuation-ring
membership and the field inverse. -/
theorem rv_eq_rv_iff_ring {x y : K} (hy : y ≠ 0) :
    rv O x = rv O y ↔ x = y ∨ ((x - y) / y)⁻¹ ∉ O := by
  rw [rv_eq_rv_iff O hy, O.mem_nonunits_iff_or, div_eq_zero_iff, sub_eq_zero,
    or_iff_left hy]

/-- The unsigned value of a nonzero leading term in mathlib's multiplicative
valuation convention, where small elements have value below one. -/
def unsignedValueUnit : RV O →* O.ValueGroup :=
  QuotientGroup.lift O.principalUnitGroup
    (O.valuation.toMonoidHom.comp (Units.coeHom K))
    (by
      intro u hu
      exact (O.mem_unitGroup_iff u).mp (O.principal_units_le_units hu))

/-- The unsigned value map, extended at RV zero. Its order is dual to the
manuscript's additive convention. -/
def unsignedValue : RV0 O →*₀ O.ValueGroup := WithZero.lift' (unsignedValueUnit O)

@[simp]
theorem unsignedValue_coe (t : RV O) :
    unsignedValue O (t : RV0 O) = unsignedValueUnit O t := by
  rw [unsignedValue, WithZero.lift'_coe]

@[simp] theorem unsignedValue_rv (x : K) : unsignedValue O (rv O x) = O.valuation x := by
  by_cases hx : x = 0
  · simp [hx]
  let u := Units.mk0 x hx
  change unsignedValue O (rv O (u : K)) = O.valuation (u : K)
  rw [rv_coe_unit, unsignedValue, WithZero.lift'_coe]
  rfl

theorem unsignedValue_surjective : Function.Surjective (unsignedValue O) := by
  intro t
  obtain ⟨x, rfl⟩ := O.valuation_surjective t
  exact ⟨rv O x, unsignedValue_rv O x⟩

theorem mem_valuationRing_iff (x : K) : x ∈ O ↔ unsignedValue O (rv O x) ≤ 1 := by
  rw [unsignedValue_rv, O.valuation_le_one_iff]

theorem mem_maximalIdeal_iff (x : K) :
    x ∈ O.nonunits ↔ unsignedValue O (rv O x) < 1 := by
  rw [unsignedValue_rv, O.mem_nonunits_iff]

theorem valuation_eq_one_iff_mem_and_inv (x : K) :
    O.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ O ∧ x⁻¹ ∈ O := by
  by_cases hx : x = 0
  · simp [hx]
  rw [O.valuation_le_one_iff x |>.symm, O.valuation_le_one_iff x⁻¹ |>.symm, map_inv₀]
  have hv : O.valuation x ≠ 0 := (map_ne_zero O.valuation).mpr hx
  rw [inv_le_one₀ (pos_iff_ne_zero.mpr hv), and_iff_right hx, le_antisymm_iff]

/-- The named witness used in §2.3 excludes the trivial valuation. -/
theorem exists_nonzero_maximalIdeal_iff :
    (∃ x : K, x ≠ 0 ∧ x ∈ O.nonunits) ↔ O.valuation.IsNontrivial := by
  simp only [O.mem_nonunits_iff]
  exact (Valuation.isNontrivial_iff_exists_lt_one O.valuation).symm

end GeneralizedEuler.Section2
