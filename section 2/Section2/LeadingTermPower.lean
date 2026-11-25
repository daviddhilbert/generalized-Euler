module

public import Section2.ConvexValuation
public import Section2.PowerBounded

/-! Descent and uniqueness of the positive RV power operation from §2.2. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

/-- The argument of the clamped power is always positive. -/
def clampForPower (x : K) : PositiveField K :=
  ⟨min 2 (max (1 / 2) x), lt_min zero_lt_two
    ((one_div_pos.mpr zero_lt_two).trans_le (le_max_left _ _))⟩

/-- The compatibility required from Ax. 8 for the clamped power. The map
on the residue field is the interpretation of the same clamped function. -/
abbrev ResidueCompatible (f : K → K)
    (residueF : IsLocalRing.ResidueField O → IsLocalRing.ResidueField O) : Prop :=
  ∀ x : O, ∃ h : f x ∈ O,
    IsLocalRing.residue O ⟨f x, h⟩ = residueF (IsLocalRing.residue O x)

/-- A multiplicative field power preserves the principal units when its
clamped total extension commutes with residue and fixes residue one. -/
theorem power_preserves_principalUnits (hO : IsOrderConvex O)
    (g : PositiveField K →* PositiveField K)
    {residueG : IsLocalRing.ResidueField O → IsLocalRing.ResidueField O}
    (hmatch : ResidueCompatible O (fun x => g (clampForPower x)) residueG)
    (hone : residueG 1 = 1) {u : Kˣ} (hu : u ∈ O.principalUnitGroup) :
    ∃ (hpos : 0 < (u : K)),
      ((g ⟨u, hpos⟩ : K) - 1) ∈ O.nonunits := by
  obtain ⟨hl, hr⟩ := principalUnit_bounds O hO hu
  have hpos : 0 < (u : K) := (one_div_pos.mpr zero_lt_two).trans hl
  have hm : (u : K) - 1 ∈ O.nonunits :=
    O.mem_nonunits_iff.mpr ((O.mem_principalUnitGroup_iff u).mp hu)
  have huO : (u : K) ∈ O :=
    (O.valuation_le_one_iff _).mp ((O.mem_unitGroup_iff u).mp
      (O.principal_units_le_units hu)).le
  let x : O := ⟨u, huO⟩
  have hx : IsLocalRing.residue O x = 1 := by
    have hzero : IsLocalRing.residue O (x - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr (O.coe_mem_nonunits_iff.mp hm)
    simpa only [map_sub, map_one, sub_eq_zero] using hzero
  have hclamp : clampForPower (x : K) = ⟨u, hpos⟩ := by
    apply Subtype.ext
    exact (congrArg (min (2 : K)) (max_eq_right hl.le)).trans (min_eq_right hr.le)
  obtain ⟨hout, hres⟩ := hmatch x
  rw [hx, hone] at hres
  let y : O := ⟨g (clampForPower (x : K)), hout⟩
  have hzero : IsLocalRing.residue O (y - 1) = 0 := by
    rw [map_sub, map_one, hres, sub_self]
  refine ⟨hpos, ?_⟩
  rw [← hclamp]
  exact O.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hzero)

/-- The positive branch of RV consists of the leading terms represented by
positive field elements. -/
abbrev IsPositiveRV (t : RV0 O) : Prop :=
  ∃ x : PositiveField K, rv O x = t

@[simp] theorem isPositiveRV_rv_iff (hO : IsOrderConvex O) {x : K} :
    IsPositiveRV O (rv O x) ↔ 0 < x :=
  ⟨fun ⟨y, hy⟩ => pos_of_rv_eq_rv O hO y.property hy.symm, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- An RV operation agrees with a positive field power on representatives. -/
abbrev AgreesWithFieldPower (g : PositiveField K →* PositiveField K)
    (P : RV0 O → RV0 O) : Prop :=
  ∀ x : PositiveField K, P (rv O x) = rv O (g x : K)

/-- Compatibility on representatives suffices to define a unique total
power operation, with zero on the other branches. -/
theorem existsUnique_leadingTermPower (g : PositiveField K →* PositiveField K)
    (hprincipal : ∀ x : PositiveField K, (x : K) - 1 ∈ O.nonunits →
      (g x : K) - 1 ∈ O.nonunits) :
    ∃! P : RV0 O → RV0 O,
      AgreesWithFieldPower O g P ∧
      (∀ t, ¬ IsPositiveRV O t → P t = 0) := by
  classical
  have hdesc : ∀ x y : PositiveField K, rv O x = rv O y →
      rv O (g x : K) = rv O (g y : K) := by
    intro x y heq
    have hxy := (rv_eq_rv_iff O y.property.ne').mp heq
    have sub_div_eq (a b : K) (hb : b ≠ 0) : (a - b) / b = a / b - 1 := by
      rw [sub_div, div_self hb]
    rw [sub_div_eq _ _ y.property.ne'] at hxy
    have coe_div (a b : PositiveField K) : ((a / b : PositiveField K) : K) =
        (a : K) / (b : K) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      rfl
    have hgxy := hprincipal (x / y) (by simpa only [coe_div] using hxy)
    apply (rv_eq_rv_iff O (g y).property.ne').mpr
    rw [sub_div_eq _ _ (g y).property.ne']
    simpa only [map_div, coe_div] using hgxy
  let P (t : RV0 O) : RV0 O :=
    if h : IsPositiveRV O t then rv O (g (Classical.choose h) : K) else 0
  have hagree (x : PositiveField K) : P (rv O x) = rv O (g x : K) := by
    have h : IsPositiveRV O (rv O x) := ⟨x, rfl⟩
    exact (dite_eq_left h).trans (hdesc _ _ (Classical.choose_spec h))
  have hoff (t : RV0 O) (h : ¬ IsPositiveRV O t) : P t = 0 := dite_eq_right h
  refine ⟨P, ⟨hagree, hoff⟩, ?_⟩
  rintro P' ⟨hpos, hnonpos⟩
  funext t
  by_cases h : IsPositiveRV O t
  · obtain ⟨x, rfl⟩ := h
    rw [hpos, hagree]
  · rw [hnonpos t h, hoff t h]

/-- Descent and uniqueness under the residue compatibility of the reviewed
clamping argument. -/
theorem existsUnique_leadingTermPower_of_residue (hO : IsOrderConvex O)
    (g : PositiveField K →* PositiveField K)
    {residueG : IsLocalRing.ResidueField O → IsLocalRing.ResidueField O}
    (hmatch : ResidueCompatible O (fun x => g (clampForPower x)) residueG)
    (hone : residueG 1 = 1) :
    ∃! P : RV0 O → RV0 O,
      AgreesWithFieldPower O g P ∧
      (∀ t, ¬ IsPositiveRV O t → P t = 0) := by
  apply existsUnique_leadingTermPower O g
  intro x hx
  let u := Units.mk0 (x : K) x.property.ne'
  have hu : u ∈ O.principalUnitGroup :=
    (O.mem_principalUnitGroup_iff u).mpr (O.mem_nonunits_iff.mp hx)
  obtain ⟨_, hg⟩ := power_preserves_principalUnits O hO g hmatch hone hu
  exact hg

/-- Multiplicativity and positivity descend to the positive RV branch. -/
theorem leadingTermPower_mul {g : PositiveField K →* PositiveField K}
    {P : RV0 O → RV0 O} (h : AgreesWithFieldPower O g P)
    {s t : RV0 O} (hs : IsPositiveRV O s) (ht : IsPositiveRV O t) :
    P (s * t) = P s * P t := by
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  rw [← map_mul (rv O), ← show ((x * y : PositiveField K) : K) = (x : K) * y from rfl,
    h, h, h, map_mul]
  exact map_mul (rv O) (g x : K) (g y : K)

theorem leadingTermPower_pos {g : PositiveField K →* PositiveField K}
    {P : RV0 O → RV0 O} (h : AgreesWithFieldPower O g P)
    {t : RV0 O} (ht : IsPositiveRV O t) : IsPositiveRV O (P t) := by
  obtain ⟨x, rfl⟩ := ht
  exact ⟨g x, (h x).symm⟩

/-- The zero, unit, addition and composition laws in Ax. 10 are inherited
from the corresponding laws of the field powers. -/
theorem leadingTermPower_scalarLaws {E : Type*} [Semiring E]
    {g : E → PositiveField K →* PositiveField K} {P : E → RV0 O → RV0 O}
    (h : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
    (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
    (hmul : ∀ e d x, g (e * d) x = g e (g d x))
    {t : RV0 O} (ht : IsPositiveRV O t) :
    P 0 t = 1 ∧ P 1 t = t ∧
      (∀ e d, P (e + d) t = P e t * P d t) ∧
      (∀ e d, P (e * d) t = P e (P d t)) := by
  obtain ⟨x, rfl⟩ := ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h 0, hzero]
    exact map_one (rv O)
  · rw [h 1, hone]
  · intro e d
    rw [h, h, h, hadd]
    exact map_mul (rv O) (g e x : K) (g d x : K)
  · intro e d
    rw [h (e * d), h d, h e, hmul]

end GeneralizedEuler.Section2
