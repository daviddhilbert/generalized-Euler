module

public import Section2.PowerOrder
public import Section2.ResidueOrder
public import Section2.ConvexRingComparison
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.LinearMap.Defs

/-! The exponent-field action on the positive leading terms in §2.2. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

/-- The leading-term quotient on the multiplicative group of positive
field elements. -/
def positiveRv (O : ValuationSubring K) : PositiveField K →* RV O where
  toFun x := rvUnit O (Units.mk0 x x.property.ne')
  map_one' := by
    have h : Units.mk0 (1 : K) one_ne_zero = (1 : Kˣ) := Units.ext rfl
    exact (congrArg (rvUnit O) h).trans (map_one (rvUnit O))
  map_mul' x y := by
    rw [← map_mul]
    apply congrArg (rvUnit O)
    exact Units.ext rfl

abbrev PositiveRV := (positiveRv O).range

def positiveRVToRV0 (t : PositiveRV O) : RV0 O := (t.val : RV0 O)

private theorem positiveRVToRV0_injective : Function.Injective (positiveRVToRV0 O) :=
  fun _ _ h => Subtype.ext (WithZero.coe_inj.mp h)

theorem positiveRVToRV0_pos (t : PositiveRV O) : IsPositiveRV O (positiveRVToRV0 O t) := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp t.property
  refine ⟨x, ?_⟩
  rw [← show ((Units.mk0 (x : K) x.property.ne' : Kˣ) : K) = x from rfl, rv_coe_unit]
  exact congrArg (fun y : RV O => (y : RV0 O)) hx

theorem exists_positiveRV_of_positive {t : RV0 O} (ht : IsPositiveRV O t) :
    ∃ s : PositiveRV O, positiveRVToRV0 O s = t := by
  obtain ⟨x, hx⟩ := ht
  exact ⟨(positiveRv O).rangeRestrict x,
    (rv_coe_unit O (Units.mk0 x x.property.ne')).symm.trans hx⟩

set_option linter.style.haveILetI false in
theorem isPositiveRV_iff_pos (hO : IsOrderConvex O) {t : RV0 O} :
    letI := rvLinearOrder O hO
    IsPositiveRV O t ↔ 0 < t := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  exact (isPositiveRV_rv_iff O hO).trans (zero_lt_rv_iff O hO).symm

@[simp]
theorem positiveRVToRV0_one : positiveRVToRV0 O (1 : PositiveRV O) = 1 := by rfl

@[simp]
theorem positiveRVToRV0_mul (s t : PositiveRV O) :
    positiveRVToRV0 O (s * t) = positiveRVToRV0 O s * positiveRVToRV0 O t := by rfl

private def positiveRVPower (g : PositiveField K →* PositiveField K)
    (t : PositiveRV O) : PositiveRV O :=
  (positiveRv O).rangeRestrict (g ((MonoidHom.mem_range.mp t.property).choose))

private theorem positiveRVToRV0_power
    {g : PositiveField K →* PositiveField K} {P : RV0 O → RV0 O}
    (hP : AgreesWithFieldPower O g P) (t : PositiveRV O) :
    positiveRVToRV0 O (positiveRVPower O g t) = P (positiveRVToRV0 O t) := by
  let x := (MonoidHom.mem_range.mp t.property).choose
  have hx : positiveRv O x = t.val := (MonoidHom.mem_range.mp t.property).choose_spec
  have hrv : rv O (x : K) = positiveRVToRV0 O t :=
    (rv_coe_unit O (Units.mk0 x x.property.ne')).trans
      (congrArg (fun y : RV O => (y : RV0 O)) hx)
  change ((positiveRv O (g x) : RV O) : RV0 O) = P (positiveRVToRV0 O t)
  rw [← hrv, hP x]
  exact (rv_coe_unit O (Units.mk0 (g x : K) (g x).property.ne')).symm

private theorem scalar_eq_of_RV0 {s t : Additive (PositiveRV O)}
    (h : positiveRVToRV0 O s.toMul = positiveRVToRV0 O t.toMul) : s = t :=
  Additive.toMul.injective (positiveRVToRV0_injective O h)

/-- The algebraic vector-space structure induced by the named power
operators. The group multiplication is written additively here. -/
@[instance_reducible]
def positiveRVModule {E : Type*} [Semiring E]
    (g : E → PositiveField K →* PositiveField K) (P : E → RV0 O → RV0 O)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
    (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
    (hmul : ∀ e d x, g (e * d) x = g e (g d x)) :
    Module E (Additive (PositiveRV O)) where
  smul e t := Additive.ofMul (positiveRVPower O (g e) t.toMul)
  one_smul t := by
    apply scalar_eq_of_RV0 O
    change positiveRVToRV0 O (positiveRVPower O (g 1) t.toMul) = positiveRVToRV0 O t.toMul
    rw [positiveRVToRV0_power O (hP 1)]
    exact (leadingTermPower_scalarLaws O hP hzero hone hadd hmul
      (positiveRVToRV0_pos O t.toMul)).2.1
  mul_smul e d t := by
    apply scalar_eq_of_RV0 O
    change positiveRVToRV0 O (positiveRVPower O (g (e * d)) t.toMul) =
      positiveRVToRV0 O (positiveRVPower O (g e) (positiveRVPower O (g d) t.toMul))
    simp only [positiveRVToRV0_power O (hP _)]
    exact (leadingTermPower_scalarLaws O hP hzero hone hadd hmul
      (positiveRVToRV0_pos O t.toMul)).2.2.2 e d
  smul_zero e := by
    apply scalar_eq_of_RV0 O
    change positiveRVToRV0 O (positiveRVPower O (g e) 1) = positiveRVToRV0 O (1 : PositiveRV O)
    rw [positiveRVToRV0_power O (hP e), positiveRVToRV0_one]
    have h := hP e (1 : PositiveField K)
    rw [map_one (g e)] at h
    change P e (rv O 1) = rv O 1 at h
    rwa [map_one (rv O)] at h
  smul_add e s t := by
    apply scalar_eq_of_RV0 O
    change positiveRVToRV0 O (positiveRVPower O (g e) (s.toMul * t.toMul)) =
      positiveRVToRV0 O (positiveRVPower O (g e) s.toMul * positiveRVPower O (g e) t.toMul)
    simp only [positiveRVToRV0_mul, positiveRVToRV0_power O (hP _)]
    exact leadingTermPower_mul O (hP e) (positiveRVToRV0_pos O s.toMul)
      (positiveRVToRV0_pos O t.toMul)
  zero_smul t := by
    apply scalar_eq_of_RV0 O
    change positiveRVToRV0 O (positiveRVPower O (g 0) t.toMul) = positiveRVToRV0 O (1 : PositiveRV O)
    rw [positiveRVToRV0_power O (hP 0), positiveRVToRV0_one]
    exact (leadingTermPower_scalarLaws O hP hzero hone hadd hmul
      (positiveRVToRV0_pos O t.toMul)).1
  add_smul e d t := by
    apply scalar_eq_of_RV0 O
    change positiveRVToRV0 O (positiveRVPower O (g (e + d)) t.toMul) =
      positiveRVToRV0 O (positiveRVPower O (g e) t.toMul * positiveRVPower O (g d) t.toMul)
    simp only [positiveRVToRV0_mul, positiveRVToRV0_power O (hP _)]
    exact (leadingTermPower_scalarLaws O hP hzero hone hadd hmul
      (positiveRVToRV0_pos O t.toMul)).2.2.1 e d

/-- The unsigned value map on positive leading terms, with values in the
nonzero value group. -/
def positiveValueMap : PositiveRV O →* O.ValueGroupˣ :=
  ((unsignedValueUnit O).comp (positiveRv O).range.subtype).toHomUnits

@[simp]
theorem positiveValueMap_coe (t : PositiveRV O) :
    (positiveValueMap O t : O.ValueGroup) = unsignedValue O (positiveRVToRV0 O t) := by
  change unsignedValueUnit O t.val = unsignedValue O (t.val : RV0 O)
  rw [unsignedValue_coe]

private theorem positiveValueMap_field (x : PositiveField K) :
    (positiveValueMap O ((positiveRv O).rangeRestrict x) : O.ValueGroup) =
      O.valuation (x : K) := by
  rw [positiveValueMap_coe]
  have hrv : positiveRVToRV0 O ((positiveRv O).rangeRestrict x) = rv O (x : K) :=
    (rv_coe_unit O (Units.mk0 x x.property.ne')).symm
  rw [hrv, unsignedValue_rv]

theorem positiveValueMap_surjective : Function.Surjective (positiveValueMap O) := by
  intro γ
  obtain ⟨x, hx⟩ := O.valuation_surjective (γ : O.ValueGroup)
  have hx0 : x ≠ 0 := (map_ne_zero O.valuation).mp (hx.trans_ne γ.ne_zero)
  let p : PositiveField K := ⟨|x|, abs_pos.mpr hx0⟩
  refine ⟨(positiveRv O).rangeRestrict p, Units.ext ?_⟩
  rw [positiveValueMap_field]
  change O.valuation |x| = _
  rw [valuation_abs, hx]

set_option linter.style.haveILetI false in
/-- The kernel of unsigned value on the positive branch is the positive
residue field. -/
def positiveValueKernelEquiv (hO : IsOrderConvex O) :
    letI := residueLinearOrder O hO
    (positiveValueMap O).ker ≃ PositiveField (Residue O) := by
  letI := residueLinearOrder O hO
  letI := rvLinearOrder O hO
  have hasResidue (x : (positiveValueMap O).ker) :
      ∃ r, residueRV O r = positiveRVToRV0 O x.val := by
    have h : positiveValueMap O x.val = 1 := x.property
    refine (Set.mem_range.mp ?_)
    rw [range_residueRV]
    right
    have he := congrArg Units.val h
    rwa [positiveValueMap_coe, Units.val_one] at he
  let R (x : (positiveValueMap O).ker) : PositiveField (Residue O) :=
    ⟨(hasResidue x).choose, by
      apply (residueRV_strictMono O hO).lt_iff_lt.mp
      rw [residueRV_zero, (hasResidue x).choose_spec]
      apply (isPositiveRV_iff_pos O hO).mp
      exact positiveRVToRV0_pos O x.val⟩
  have hR (x : (positiveValueMap O).ker) :
      residueRV O (R x : Residue O) = positiveRVToRV0 O x.val :=
    (hasResidue x).choose_spec
  refine Equiv.ofBijective R ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply positiveRVToRV0_injective O
    rw [← hR, ← hR, h]
  · intro r
    have hpos : 0 < residueRV O (r : Residue O) := by
      have h := residueRV_strictMono O hO r.property
      rwa [residueRV_zero] at h
    obtain ⟨t, ht⟩ := exists_positiveRV_of_positive O ((isPositiveRV_iff_pos O hO).mpr hpos)
    have hval : t ∈ (positiveValueMap O).ker := by
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      rw [positiveValueMap_coe, ht, Units.val_one]
      exact unsignedValue_residueRV_of_ne_zero O r.property.ne'
    refine ⟨⟨t, hval⟩, Subtype.ext (residueRV_injective O ?_)⟩
    exact (hR ⟨t, hval⟩).trans ht

private theorem positiveValueMap_power_congr
    (g : PositiveField K →* PositiveField K) {P : RV0 O → RV0 O}
    (hP : AgreesWithFieldPower O g P)
    (hunit : ∀ x : PositiveField K, O.valuation (x : K) = 1 →
      O.valuation (g x : K) = 1)
    {s t : PositiveRV O} (hst : positiveValueMap O s = positiveValueMap O t) :
    positiveValueMap O (positiveRVPower O g s) = positiveValueMap O (positiveRVPower O g t) := by
  obtain ⟨x, hx⟩ := positiveRVToRV0_pos O s
  obtain ⟨y, hy⟩ := positiveRVToRV0_pos O t
  have h := congrArg Units.val hst
  rw [positiveValueMap_coe, positiveValueMap_coe, ← hx, ← hy,
    unsignedValue_rv, unsignedValue_rv] at h
  apply Units.ext
  rw [positiveValueMap_coe, positiveValueMap_coe, positiveRVToRV0_power O hP,
    positiveRVToRV0_power O hP, ← hx, ← hy, hP x, hP y, unsignedValue_rv, unsignedValue_rv]
  exact power_respects_unsignedValue O g hunit h

private def valueScalar {E : Type*} (g : E → PositiveField K →* PositiveField K)
    (e : E) (γ : Additive (O.ValueGroupˣ)) : Additive (O.ValueGroupˣ) :=
  Additive.ofMul (positiveValueMap O (positiveRVPower O (g e)
    ((positiveValueMap_surjective O γ.toMul).choose)))

private theorem valueScalar_eq {E : Type*} (g : E → PositiveField K →* PositiveField K)
    (P : E → RV0 O → RV0 O) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 →
      O.valuation (g e x : K) = 1) (e : E) (t : PositiveRV O) :
    valueScalar O g e (Additive.ofMul (positiveValueMap O t)) =
      Additive.ofMul (positiveValueMap O (positiveRVPower O (g e) t)) := by
  apply congrArg Additive.ofMul
  exact positiveValueMap_power_congr O (g e) (hP e) (hunit e)
    (positiveValueMap_surjective O (positiveValueMap O t)).choose_spec

section ValueModule

variable {E : Type*} [Semiring E]
  (g : E → PositiveField K →* PositiveField K) (P : E → RV0 O → RV0 O)
  (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

/-- The exponent action descends along the unsigned value map. -/
@[instance_reducible]
def unsignedValueModule : Module E (Additive (O.ValueGroupˣ)) := by
  letI := positiveRVModule O g P hP hzero hone hadd hmul
  letI : SMul E (Additive (O.ValueGroupˣ)) := ⟨valueScalar O g⟩
  let f : Additive (PositiveRV O) →+ Additive (O.ValueGroupˣ) := (positiveValueMap O).toAdditive
  have hf : Function.Surjective f := positiveValueMap_surjective O
  exact Function.Surjective.module E f hf (fun e (t : Additive (PositiveRV O)) =>
    (valueScalar_eq O g P hP hunit e t.toMul).symm)

set_option linter.style.haveILetI false in
/-- The map to unsigned values is a surjective linear map over the exponent
field. It is the map used in the base-compatible splitting of Lemma 2.29. -/
def positiveValueLinearMap :
    letI := positiveRVModule O g P hP hzero hone hadd hmul
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    Additive (PositiveRV O) →ₗ[E] Additive (O.ValueGroupˣ) := by
  letI := positiveRVModule O g P hP hzero hone hadd hmul
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  exact { (positiveValueMap O).toAdditive with
    map_smul' := fun e t => (valueScalar_eq O g P hP hunit e t.toMul).symm }

theorem positiveValueLinearMap_surjective :
    Function.Surjective (positiveValueLinearMap O g P hP hzero hone hadd hmul hunit) := by
  exact positiveValueMap_surjective O

omit [Semiring E] in
include hP in
private theorem positiveRVPower_field (e : E) (x : PositiveField K) :
    positiveRVPower O (g e) ((positiveRv O).rangeRestrict x) =
      (positiveRv O).rangeRestrict (g e x) := by
  apply positiveRVToRV0_injective O
  rw [positiveRVToRV0_power O (hP e)]
  simpa only [show ∀ y : PositiveField K,
    positiveRVToRV0 O ((positiveRv O).rangeRestrict y) = rv O (y : K) from
      fun y => (rv_coe_unit O (Units.mk0 y y.property.ne')).symm] using hP e x

set_option linter.style.haveILetI false in
/-- Coarsening a valuation commutes with the exponent action when both
value spaces are induced by the same field powers. -/
def valueCoarseningLinearMap (Q : ValuationSubring K) (h : O ≤ Q)
    (R : E → RV0 Q → RV0 Q) (hR : ∀ e, AgreesWithFieldPower Q (g e) (R e))
    (hunitQ : ∀ e (x : PositiveField K), Q.valuation (x : K) = 1 →
      Q.valuation (g e x : K) = 1) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    letI := unsignedValueModule Q g R hR hzero hone hadd hmul hunitQ
    Additive (O.ValueGroupˣ) →ₗ[E] Additive (Q.ValueGroupˣ) := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  letI := unsignedValueModule Q g R hR hzero hone hadd hmul hunitQ
  have onField (x : PositiveField K) :
      valueCoarseningUnits O Q h (positiveValueMap O ((positiveRv O).rangeRestrict x)) =
        positiveValueMap Q ((positiveRv Q).rangeRestrict x) := by
    apply Units.ext
    rw [valueCoarseningUnits_coe, positiveValueMap_field, positiveValueMap_field,
      ValuationSubring.mapOfLE_valuation_apply]
  refine { (valueCoarseningUnits O Q h).toAdditive with map_smul' := ?_ }
  intro e γ
  obtain ⟨t, ht⟩ := positiveValueMap_surjective O γ.toMul
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp t.property
  have hx' : (positiveRv O).rangeRestrict x = t := Subtype.ext hx
  rw [← hx'] at ht
  have hγ : γ = Additive.ofMul (positiveValueMap O ((positiveRv O).rangeRestrict x)) :=
    congrArg Additive.ofMul ht.symm
  subst γ
  change Additive.ofMul (valueCoarseningUnits O Q h
      (valueScalar O g e (Additive.ofMul (positiveValueMap O
        ((positiveRv O).rangeRestrict x)))).toMul) =
    valueScalar Q g e (Additive.ofMul (valueCoarseningUnits O Q h
      (positiveValueMap O ((positiveRv O).rangeRestrict x))))
  rw [valueScalar_eq O g P hP hunit, positiveRVPower_field O g P hP]
  rw [onField x, valueScalar_eq Q g R hR hunitQ, positiveRVPower_field Q g R hR]
  exact congrArg Additive.ofMul (onField (g e x))

end ValueModule

section RelativeRank

variable {E : Type*} [Field E]
  (g : E → PositiveField K →* PositiveField K)
  (P : E → RV0 O → RV0 O) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

set_option linter.style.haveILetI false in
/-- Comparison in the new-value case of Theorem 2.16. If the value
coarsening is injective on the old subspace and keeps a new generator
outside its image, the relative rank bound forces equality of the rings. -/
theorem eq_of_coarsening_preserving_new_value (Q : ValuationSubring K) (h : O ≤ Q)
    (R : E → RV0 Q → RV0 Q) (hR : ∀ e, AgreesWithFieldPower Q (g e) (R e))
    (hunitQ : ∀ e (x : PositiveField K), Q.valuation (x : K) = 1 →
      Q.valuation (g e x : K) = 1) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    letI := unsignedValueModule Q g R hR hzero hone hadd hmul hunitQ
    let f := valueCoarseningLinearMap O g P hP hzero hone hadd hmul hunit Q h R hR hunitQ
    ∀ (U : Submodule E (Additive (O.ValueGroupˣ))) [FiniteDimensional E (_ ⧸ U)],
      Module.finrank E (_ ⧸ U) ≤ 1 →
      Set.InjOn f U → ∀ a, f a ∉ U.map f → O = Q := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  letI := unsignedValueModule Q g R hR hzero hone hadd hmul hunitQ
  intro f U _ hd hU a ha
  have ha' : a ∉ U := fun hm => ha (Submodule.mem_map_of_mem hm)
  have hspan := span_base_and_new_value_of_relative_finrank_le_one U hd ha'
  have hf := injective_valueMap_of_base_and_generator f U hspan hU ha
  apply eq_of_injective_valueCoarseningUnits O Q h
  intro x y hxy
  exact congrArg Additive.toMul (hf (congrArg Additive.ofMul hxy))

end RelativeRank

end GeneralizedEuler.Section2
