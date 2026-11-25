module

public import Section2.RVVectorSpace

/-! Comparison of the valuations on a common one-generator field
extension via its relative value rank. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field E]
  (O : ValuationSubring K) (g : E → PositiveField K →* PositiveField K)
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (A : Subfield K)
  (hA : ∀ e (x : PositiveField K), (x : K) ∈ A → (g e x : K) ∈ A)

variable (P : E → RV0 O → RV0 O) (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

set_option linter.style.haveILetI false in
/-- The old value group is a subspace, since positive base elements
remain in the base under all named powers. -/
def oldValueSubspace :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    Submodule E (Additive (O.ValueGroupˣ)) := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  refine
    { carrier := Set.range (fun x : {x : PositiveField K // (x : K) ∈ A} => positiveFieldValue O x.val)
      zero_mem' := by
        refine ⟨⟨1, A.one_mem⟩, ?_⟩
        apply Units.ext
        change ((positiveFieldValue O 1).toMul : O.ValueGroup) = 1
        rw [positiveFieldValue_coe]
        exact map_one O.valuation
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        refine ⟨⟨x.val * y.val, A.mul_mem x.property y.property⟩, ?_⟩
        apply Units.ext
        change ((positiveFieldValue O (x.val * y.val)).toMul : O.ValueGroup) =
          ((positiveFieldValue O x.val).toMul : O.ValueGroup) *
          ((positiveFieldValue O y.val).toMul : O.ValueGroup)
        rw [positiveFieldValue_coe, positiveFieldValue_coe, positiveFieldValue_coe]
        exact map_mul O.valuation (x.val : K) (y.val : K)
      smul_mem' := by
        rintro e _ ⟨x, rfl⟩
        exact ⟨⟨g e x.val, hA e x.val x.property⟩,
          positiveFieldValue_power O g P hP hzero hone hadd hmul hunit e x.val⟩ }

set_option linter.style.haveILetI false in
theorem exists_positive_representative_of_mem_oldValueSubspace (z : Additive (O.ValueGroupˣ)) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    z ∈ oldValueSubspace O g hzero hone hadd hmul A hA P hP hunit →
      ∃ x : PositiveField K, (x : K) ∈ A ∧ positiveFieldValue O x = z := by
  rintro ⟨x, hx⟩
  exact ⟨x.val, x.property, hx⟩

set_option linter.style.haveILetI false in
theorem mem_oldValueSubspace_iff (z : Additive (O.ValueGroupˣ)) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    z ∈ oldValueSubspace O g hzero hone hadd hmul A hA P hP hunit ↔
      (z.toMul : O.ValueGroup) ∈ O.valuation '' (A : Set K) := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  change (∃ x : {x : PositiveField K // (x : K) ∈ A}, positiveFieldValue O x.val = z) ↔ _
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, (positiveFieldValue_coe O x.val).symm⟩
  · rintro ⟨x, hx, hv⟩
    have hx0 : x ≠ 0 := (map_ne_zero O.valuation).mp (hv.trans_ne z.toMul.ne_zero)
    let p : PositiveField K := ⟨|x|, abs_pos.mpr hx0⟩
    have habs : (p : K) ∈ A := by
      change x ∈ A at hx
      change |x| ∈ A
      rcases le_or_gt 0 x with h | h
      · simpa only [abs_of_nonneg h] using hx
      · simpa only [abs_of_neg h] using A.neg_mem hx
    refine ⟨⟨p, habs⟩, ?_⟩
    apply Units.ext
    change ((positiveFieldValue O p).toMul : O.ValueGroup) = (z.toMul : O.ValueGroup)
    rw [positiveFieldValue_coe]
    change O.valuation |x| = _
    rw [valuation_abs, hv]

set_option linter.style.haveILetI false in
/-- The value-group consequence of the Wilkie bound for a
one-generator extension over the specified old field. -/
@[expose]
def RelativeValueRankLEOne : Prop :=
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  let U := oldValueSubspace O g hzero hone hadd hmul A hA P hP hunit
  ∃ (_ : FiniteDimensional E (Additive (O.ValueGroupˣ) ⧸ U)),
    Module.finrank E (Additive (O.ValueGroupˣ) ⧸ U) ≤ 1

set_option linter.style.haveILetI false in
/-- If each leading term is an old factor times a power of one
generator, its value spans the relative value group. This applies to
the leading-term formula over a trivially valued base. -/
theorem relativeValueRankLEOne_of_monomials (a : PositiveField K)
    (hnormal : ∀ x : K, x ≠ 0 → ∃ d ∈ A, ∃ e : E, rv O x = rv O d * P e (rv O a.val)) :
    RelativeValueRankLEOne O g hzero hone hadd hmul A hA P hP hunit := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  let U := oldValueSubspace O g hzero hone hadd hmul A hA P hP hunit
  let f := LinearMap.toSpanSingleton E (_ ⧸ U) (U.mkQ (positiveFieldValue O a))
  have hOnto : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := U.mkQ_surjective y
    obtain ⟨x, hx⟩ := O.valuation_surjective (z.toMul : O.ValueGroup)
    have hx0 : x ≠ 0 := (map_ne_zero O.valuation).mp (hx.trans_ne z.toMul.ne_zero)
    obtain ⟨d, hd, e, he⟩ := hnormal x hx0
    have hv := congrArg (unsignedValue O) he
    rw [hP e a, ← map_mul, unsignedValue_rv, unsignedValue_rv, map_mul] at hv
    have hd0 : d ≠ 0 := by
      intro hd0
      rw [hd0, map_zero, zero_mul] at hv
      exact ((map_ne_zero O.valuation).mpr hx0) hv
    let c : PositiveField K := ⟨|d|, abs_pos.mpr hd0⟩
    have hc : positiveFieldValue O c ∈ U := by
      apply (mem_oldValueSubspace_iff O g hzero hone hadd hmul A hA P hP hunit _).mpr
      refine ⟨d, hd, ?_⟩
      rw [positiveFieldValue_coe]
      exact (valuation_abs O d).symm
    have hz : z = positiveFieldValue O c + e • positiveFieldValue O a := by
      apply Units.ext
      change (z.toMul : O.ValueGroup) = (positiveFieldValue O c).toMul *
        (e • positiveFieldValue O a).toMul
      rw [← hx, ← positiveFieldValue_power O g P hP hzero hone hadd hmul hunit,
        positiveFieldValue_coe, positiveFieldValue_coe]
      change O.valuation x = O.valuation |d| * O.valuation (g e a : K)
      rw [valuation_abs]
      exact hv
    refine ⟨e, ?_⟩
    have hc0 : U.mkQ (positiveFieldValue O c) = 0 := by
      have hm : positiveFieldValue O c ∈ LinearMap.ker U.mkQ := by
        rw [Submodule.ker_mkQ]
        exact hc
      exact LinearMap.mem_ker.mp hm
    change e • U.mkQ (positiveFieldValue O a) = U.mkQ z
    rw [hz, map_add, map_smul, hc0, zero_add]
  refine ⟨FiniteDimensional.of_surjective f hOnto, ?_⟩
  simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_surjective hOnto

variable (Q : ValuationSubring K)
  (R : E → RV0 Q → RV0 Q) (hR : ∀ e, AgreesWithFieldPower Q (g e) (R e))
  (hunitQ : ∀ e (x : PositiveField K), Q.valuation (x : K) = 1 → Q.valuation (g e x : K) = 1)

set_option linter.style.haveILetI false in
include hR hunitQ in
private theorem eq_of_coarsening_of_relative_rank (h : O ≤ Q)
    (hbase : ∀ x ∈ A, x ∈ O ↔ x ∈ Q)
    (hrank : RelativeValueRankLEOne O g hzero hone hadd hmul A hA P hP hunit)
    (a : PositiveField K) (ha : Q.valuation (a : K) ∉ Q.valuation '' (A : Set K)) : O = Q := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  letI := unsignedValueModule Q g R hR hzero hone hadd hmul hunitQ
  let U := oldValueSubspace O g hzero hone hadd hmul A hA P hP hunit
  let f := valueCoarseningLinearMap O g P hP hzero hone hadd hmul hunit Q h R hR hunitQ
  have hU (x : Additive (O.ValueGroupˣ)) :
      x ∈ U ↔ (x.toMul : O.ValueGroup) ∈ O.valuation '' (A : Set K) :=
    mem_oldValueSubspace_iff O g hzero hone hadd hmul A hA P hP hunit x
  have hf (x : Additive (O.ValueGroupˣ)) : ((f x).toMul : Q.ValueGroup) =
      ValuationSubring.mapOfLE O Q h (x.toMul : O.ValueGroup) :=
    valueCoarseningLinearMap_coe O g P hP hzero hone hadd hmul hunit Q h R hR hunitQ x
  have hInj : Set.InjOn f U := by
    intro x hx y hy he
    apply Units.ext
    change (x.toMul : O.ValueGroup) = (y.toMul : O.ValueGroup)
    exact coarsening_injOn_base_values O Q A h hbase ((hU x).mp hx) ((hU y).mp hy) (by
      rw [← hf, ← hf, he])
  have hnew : f (positiveFieldValue O a) ∉ U.map f := by
    rintro ⟨z, hz, he⟩
    obtain ⟨c, hc, hcz⟩ := (hU z).mp hz
    apply ha
    refine ⟨c, hc, ?_⟩
    have hv := congrArg (fun x : Additive (Q.ValueGroupˣ) => (x.toMul : Q.ValueGroup)) he
    rw [hf, hf, positiveFieldValue_coe, ← hcz,
      ValuationSubring.mapOfLE_valuation_apply, ValuationSubring.mapOfLE_valuation_apply] at hv
    exact hv
  obtain ⟨hfinite, hd⟩ := hrank
  letI : FiniteDimensional E (Additive (O.ValueGroupˣ) ⧸ U) := hfinite
  exact eq_of_coarsening_preserving_new_value O g P hP hzero hone hadd hmul hunit Q h R hR hunitQ
    U hd hInj (positiveFieldValue O a) hnew

/-- If the two valuations agree on the old field and the chosen
generator has a new value for each, the Wilkie bounds force the rings
to coincide. This argument also handles a trivially valued base. -/
theorem eq_convexValuationRing_of_rank_one_and_new_values
    (hO : IsOrderConvex O) (hQ : IsOrderConvex Q)
    (hbase : ∀ x ∈ A, x ∈ O ↔ x ∈ Q)
    (hrankO : RelativeValueRankLEOne O g hzero hone hadd hmul A hA P hP hunit)
    (hrankQ : RelativeValueRankLEOne Q g hzero hone hadd hmul A hA R hR hunitQ)
    (a : PositiveField K) (haO : O.valuation (a : K) ∉ O.valuation '' (A : Set K))
    (haQ : Q.valuation (a : K) ∉ Q.valuation '' (A : Set K)) : O = Q := by
  rcases convexValuationRing_comparable O Q hO hQ with h | h
  · exact eq_of_coarsening_of_relative_rank O g hzero hone hadd hmul A hA P hP hunit Q R hR hunitQ
      h hbase hrankO a haQ
  · exact (eq_of_coarsening_of_relative_rank Q g hzero hone hadd hmul A hA R hR hunitQ O P hP hunit
      h (fun x hx => (hbase x hx).symm) hrankQ a haO).symm

/-- The Wilkie alternatives determine the valuation on the common
adjunction. If the generator has old value, all values are old for
both valuations. In the other case the common generator has new
value and the relative rank bounds apply. -/
theorem eq_convexValuationRing_of_wilkie_value_cases
    (hO : IsOrderConvex O) (hQ : IsOrderConvex Q)
    (hbase : ∀ x ∈ A, x ∈ O ↔ x ∈ Q)
    (hrankO : RelativeValueRankLEOne O g hzero hone hadd hmul A hA P hP hunit)
    (hrankQ : RelativeValueRankLEOne Q g hzero hone hadd hmul A hA R hR hunitQ)
    (a : PositiveField K)
    (hOldEq : O.valuation (a : K) ∈ O.valuation '' (A : Set K) ↔
      Q.valuation (a : K) ∈ Q.valuation '' (A : Set K))
    (hOldO : O.valuation (a : K) ∈ O.valuation '' (A : Set K) →
      ∀ u, u ∈ O.valuation '' (A : Set K))
    (hOldQ : Q.valuation (a : K) ∈ Q.valuation '' (A : Set K) →
      ∀ u, u ∈ Q.valuation '' (A : Set K)) : O = Q := by
  by_cases ha : O.valuation (a : K) ∈ O.valuation '' (A : Set K)
  · exact eq_convexValuationRing_of_all_values_old O Q hO hQ A hbase (hOldO ha) (hOldQ (hOldEq.mp ha))
  · exact eq_convexValuationRing_of_rank_one_and_new_values O g hzero hone hadd hmul A hA P hP hunit
      Q R hR hunitQ hO hQ hbase hrankO hrankQ a ha (hOldEq.not.mp ha)

end GeneralizedEuler.Section2
