module

public import Section2.LeadingTermOrder
public import Section2.ValueSplitting
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! Comparison of convex valuation rings in the prescribed-lift proof. -/

public section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O P : ValuationSubring K)

private theorem mem_of_abs_le_mem {x y : K} (hO : IsOrderConvex O) (hy : y ∈ O)
    (hxy : |x| ≤ |y|) : x ∈ O := by
  have habs : |y| ∈ O := by
    rcases le_or_gt 0 y with h | h
    · simpa only [abs_of_nonneg h] using hy
    · simpa only [abs_of_neg h] using O.neg_mem y hy
  exact hO.out (O.neg_mem _ habs) habs (abs_le.mp hxy)

/-- Equality of leading terms for a convex valuation forces equality of
unsigned values for every convex valuation on the same ordered field. -/
theorem value_eq_of_rv_eq_for_convex_valuations (hO : IsOrderConvex O)
    (hP : IsOrderConvex P) {x y : K} (hxy : rv O x = rv O y) :
    P.valuation x = P.valuation y := by
  by_cases hy : y = 0
  · subst y
    rw [map_zero, rv_eq_zero_iff] at hxy
    rw [hxy]
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, map_zero, eq_comm, rv_eq_zero_iff] at hxy
    exact hy hxy
  let u := Units.mk0 (x / y) (div_ne_zero hx hy)
  have hunit : u ∈ O.principalUnitGroup := by
    apply (O.mem_principalUnitGroup_iff u).mpr
    apply O.mem_nonunits_iff.mp
    change x / y - 1 ∈ O.nonunits
    rw [← div_self hy, ← sub_div]
    exact (rv_eq_rv_iff O hy).mp hxy
  have htwo : (2 : K) ∈ P := by
    rw [← one_add_one_eq_two]
    exact P.add_mem 1 1 P.one_mem P.one_mem
  have mem_of_bounds (v : Kˣ) (hv : v ∈ O.principalUnitGroup) : (v : K) ∈ P := by
    obtain ⟨hl, hr⟩ := principalUnit_bounds O hO hv
    have hpos : (0 : K) ≤ 1 / 2 := by positivity
    exact hP.out P.zero_mem htwo ⟨hpos.trans hl.le, hr.le⟩
  have hv := (valuation_eq_one_iff_mem_and_inv P (x / y)).mpr
    ⟨u.ne_zero, mem_of_bounds u hunit, mem_of_bounds u⁻¹ (O.principalUnitGroup.inv_mem hunit)⟩
  rw [map_div₀] at hv
  exact (div_eq_one_iff_eq ((map_ne_zero P.valuation).mpr hy)).mp hv

/-- A translate with a new value for the finer convex ring has a new
leading term for the coarser ring, as needed in Lemma 2.22. -/
theorem rv_not_mem_range_of_new_fine_value (hO : IsOrderConvex O)
    (hP : IsOrderConvex P) {A : Set K} {x : K}
    (hx : P.valuation x ∉ P.valuation '' A) : rv O x ∉ rv O '' A := by
  rintro ⟨y, hy, h⟩
  exact hx ⟨y, hy, value_eq_of_rv_eq_for_convex_valuations O P hO hP h⟩

/-- Convex valuation rings of the same ordered field are comparable. -/
theorem convexValuationRing_comparable (hO : IsOrderConvex O) (hP : IsOrderConvex P) :
    O ≤ P ∨ P ≤ O := by
  by_cases h : O ≤ P
  · exact Or.inl h
  right
  have hh : ¬ ∀ x : K, x ∈ O → x ∈ P := h
  rw [not_forall] at hh
  obtain ⟨x, hx⟩ := hh
  have hxO : x ∈ O := by
    by_contra h
    exact hx (fun ha => (h ha).elim)
  have hxP : x ∉ P := fun hp => hx (fun _ => hp)
  intro y hy
  rcases le_total |y| |x| with h | h
  · exact mem_of_abs_le_mem O hO hxO h
  · exact (hxP (mem_of_abs_le_mem P hP hy h)).elim

/-- The cut between the absolute values of the old valuation ring and
the absolute values of its complement in the old field. -/
def RealizesValuationRingCut (A : Set K) (x : K) : Prop :=
  (∀ y ∈ A, y ∈ O → |y| < x) ∧ (∀ y ∈ A, y ∉ O → x < |y|)

private theorem realizes_cut_of_mem_difference (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    {A : Set K} (hA : ∀ y ∈ A, y ∈ O ↔ y ∈ P) {x : K} (hxP : x ∈ P) (hxO : x ∉ O) :
    RealizesValuationRingCut O A |x| := by
  constructor
  · intro y _ hy
    exact lt_of_not_ge (fun h => hxO (mem_of_abs_le_mem O hO hy h))
  · intro y hyA hy
    exact lt_of_not_ge (fun h => hy ((hA y hyA).mpr (mem_of_abs_le_mem P hP hxP h)))

/-- A difference between two convex rings that have the same old ring
would realize its cut. This proves the ring comparison in Case (2) of
the prescribed-lift argument. -/
theorem eq_convexValuationRing_of_no_cut (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    {A : Set K} (hA : ∀ y ∈ A, y ∈ O ↔ y ∈ P)
    (hn : ∀ x, ¬ RealizesValuationRingCut O A x) : O = P := by
  rcases convexValuationRing_comparable O P hO hP with h | h
  · apply le_antisymm h
    intro x hx
    by_contra hxO
    exact hn |x| (realizes_cut_of_mem_difference O P hO hP hA hx hxO)
  · refine le_antisymm ?_ h
    intro x hx
    by_contra hxP
    have hcut := realizes_cut_of_mem_difference P O hP hO
      (fun y hy => (hA y hy).symm) hx hxP
    exact hn |x| ⟨fun y hy hyO => hcut.1 y hy ((hA y hy).mp hyO),
      fun y hy hyO => hcut.2 y hy (hyO ∘ (hA y hy).mpr)⟩

/-- If the rings induce the same old ring and agree on the realizations
of its cut, comparability forces the rings to coincide. -/
theorem eq_convexValuationRing_of_agree_on_cut (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    {A : Set K} (hA : ∀ y ∈ A, y ∈ O ↔ y ∈ P)
    (hcut : ∀ x, RealizesValuationRingCut O A x → (x ∈ O ↔ x ∈ P)) : O = P := by
  rcases convexValuationRing_comparable O P hO hP with hOP | hPO
  · refine le_antisymm hOP ?_
    intro x hxP
    by_contra hxO
    have hc := realizes_cut_of_mem_difference O P hO hP hA hxP hxO
    have hm : |x| ∈ P := mem_of_abs_le_mem P hP hxP (by rw [abs_abs])
    exact hxO (mem_of_abs_le_mem O hO ((hcut _ hc).mpr hm) (by rw [abs_abs]))
  · refine le_antisymm ?_ hPO
    intro x hxO
    by_contra hxP
    have hc := realizes_cut_of_mem_difference P O hP hO (fun y hy => (hA y hy).symm) hxO hxP
    have hc' : RealizesValuationRingCut O A |x| :=
      ⟨fun y hy h => hc.1 y hy ((hA y hy).mp h), fun y hy h => hc.2 y hy (h ∘ (hA y hy).mpr)⟩
    have hm : |x| ∈ O := mem_of_abs_le_mem O hO hxO (by rw [abs_abs])
    exact hxP (mem_of_abs_le_mem P hP ((hcut _ hc').mp hm) (by rw [abs_abs]))

/-- The two classifications of the old cut agree once the rings make the
same choice on a single realization that decides membership on the cut. -/
theorem eq_convexValuationRing_of_cut_membership (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    {A : Set K} (hA : ∀ y ∈ A, y ∈ O ↔ y ∈ P) (a : K)
    (hOcut : ∀ x, RealizesValuationRingCut O A x → (x ∈ O ↔ a ∈ O))
    (hPcut : ∀ x, RealizesValuationRingCut O A x → (x ∈ P ↔ a ∈ P))
    (ha : a ∈ O ↔ a ∈ P) : O = P :=
  eq_convexValuationRing_of_agree_on_cut O P hO hP hA
    (fun x hx => (hOcut x hx).trans (ha.trans (hPcut x hx).symm))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- If the value-group map of a coarsening is injective, the two valuation
rings coincide. -/
theorem eq_of_injective_valueCoarsening (h : O ≤ P)
    (hinj : Function.Injective (ValuationSubring.mapOfLE O P h)) : O = P := by
  apply le_antisymm h
  intro x hx
  by_contra ho
  have hv : 1 < O.valuation x := by
    apply lt_of_not_ge
    exact fun hx' => ho ((O.valuation_le_one_iff x).mp hx')
  have hle : 1 ≤ P.valuation x := by
    have hm := ValuationSubring.monotone_mapOfLE O P h hv.le
    simpa only [map_one, ValuationSubring.mapOfLE_valuation_apply] using hm
  have heq : P.valuation x = 1 := ((P.valuation_le_one_iff x).mpr hx).antisymm hle
  have hm : ValuationSubring.mapOfLE O P h (O.valuation x) =
      ValuationSubring.mapOfLE O P h 1 := by
    rw [ValuationSubring.mapOfLE_valuation_apply, map_one, heq]
  exact hv.ne' (hinj hm)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The coarsening homomorphism on nonzero unsigned values. -/
noncomputable def valueCoarseningUnits (h : O ≤ P) : O.ValueGroupˣ →* P.ValueGroupˣ :=
  Units.map (ValuationSubring.mapOfLE O P h).toMonoidHom

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem valueCoarseningUnits_coe (h : O ≤ P) (x : O.ValueGroupˣ) :
    (valueCoarseningUnits O P h x : P.ValueGroup) = ValuationSubring.mapOfLE O P h x := by
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem eq_of_injective_valueCoarseningUnits (h : O ≤ P)
    (hinj : Function.Injective (valueCoarseningUnits O P h)) : O = P := by
  apply eq_of_injective_valueCoarsening O P h
  intro x y hxy
  by_cases hx : x = 0
  · subst x
    rw [map_zero, eq_comm, map_eq_zero] at hxy
    exact hxy.symm
  · have hy : y ≠ 0 := by
      intro hy
      subst y
      rw [map_zero, map_eq_zero] at hxy
      exact hx hxy
    let xu := Units.mk0 x hx
    let yu := Units.mk0 y hy
    have hu : valueCoarseningUnits O P h xu = valueCoarseningUnits O P h yu :=
      Units.ext hxy
    exact congrArg Units.val (hinj hu)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A coarsening of the ambient rings is injective on the values from
any base subfield on which the two rings induce the same valuation ring. -/
theorem coarsening_injOn_base_values (A : Subfield K) (h : O ≤ P)
    (hA : ∀ x ∈ A, x ∈ O ↔ x ∈ P) :
    Set.InjOn (ValuationSubring.mapOfLE O P h) (O.valuation '' (A : Set K)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  rw [ValuationSubring.mapOfLE_valuation_apply, ValuationSubring.mapOfLE_valuation_apply] at hxy
  by_cases hy0 : y = 0
  · subst y
    rw [map_zero, map_eq_zero] at hxy
    simp [hxy]
  have hvP : P.valuation y ≠ 0 := (map_ne_zero P.valuation).mpr hy0
  have hvO : O.valuation y ≠ 0 := (map_ne_zero O.valuation).mpr hy0
  have hquot : P.valuation (x / y) = 1 := by
    rw [map_div₀, hxy, div_self hvP]
  obtain ⟨hne, hmem, hinv⟩ := (valuation_eq_one_iff_mem_and_inv P _).mp hquot
  have hz : x / y ∈ A := A.div_mem hx hy
  have h₁ := (valuation_eq_one_iff_mem_and_inv O _).mpr
    ⟨hne, (hA _ hz).mpr hmem, (hA _ (A.inv_mem hz)).mpr hinv⟩
  rw [map_div₀] at h₁
  exact (div_eq_one_iff_eq hvO).mp h₁

/-- In the unchanged-value case both convex rings are uniquely determined
by the old valuation ring. -/
theorem eq_convexValuationRing_of_all_values_old (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (A : Subfield K) (hA : ∀ x ∈ A, x ∈ O ↔ x ∈ P)
    (hOldO : ∀ u, u ∈ O.valuation '' (A : Set K))
    (hOldP : ∀ u, u ∈ P.valuation '' (A : Set K)) : O = P := by
  rcases convexValuationRing_comparable O P hO hP with h | h
  · apply eq_of_injective_valueCoarsening O P h
    intro x y hxy
    exact coarsening_injOn_base_values O P A h hA (hOldO x) (hOldO y) hxy
  · symm
    apply eq_of_injective_valueCoarsening P O h
    intro x y hxy
    exact coarsening_injOn_base_values P O A h (fun z hz => (hA z hz).symm)
      (hOldP x) (hOldP y) hxy

/-- A coarsening is injective on a value group spanned by the old values
and one new value if it is injective on the base and the new value
stays outside the base image. -/
theorem injective_valueMap_of_base_and_generator
    {E V W : Type*} [Field E] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]
    (f : V →ₗ[E] W) (U : Submodule E V) {a : V}
    (hspan : U ⊔ Submodule.span E {a} = ⊤)
    (hU : Set.InjOn f U) (ha : f a ∉ U.map f) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  refine eq_bot_iff.mpr ?_
  intro x hx
  have hm : x ∈ U ⊔ Submodule.span E {a} := hspan ▸ Submodule.mem_top
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hc
  have hzero := LinearMap.mem_ker.mp hx
  rw [map_add, map_smul] at hzero
  have hr0 : r = 0 := by
    by_contra hr
    have hs : r • f a ∈ U.map f := by
      have heq : r • f a = -f b := eq_neg_of_add_eq_zero_right hzero
      rw [heq]
      exact (U.map f).neg_mem (Submodule.mem_map_of_mem hb)
    have hv := (U.map f).smul_mem r⁻¹ hs
    exact ha (by simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hv)
  rw [hr0, zero_smul, add_zero] at hzero ⊢
  have hb0 : b = 0 := hU hb U.zero_mem (hzero.trans (map_zero f).symm)
  rw [hb0]
  exact Submodule.zero_mem _

/-- The trivial-base case of the one-generator coarsening criterion. -/
theorem injective_valueMap_of_span_singleton
    {E V W : Type*} [Field E] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]
    (f : V →ₗ[E] W) {a : V} (hspan : Submodule.span E {a} = ⊤) (ha : f a ≠ 0) :
    Function.Injective f := by
  apply injective_valueMap_of_base_and_generator f ⊥ (a := a) (by rwa [bot_sup_eq])
  · intro b hb c hc _
    exact ((Submodule.mem_bot E).mp hb).trans ((Submodule.mem_bot E).mp hc).symm
  · simpa only [Submodule.map_bot, Submodule.mem_bot] using ha

/-- The relative value-rank bound supplied by the Wilkie inequality
makes any new value a generator modulo the old value space. -/
theorem span_base_and_new_value_of_relative_finrank_le_one
    {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (U : Submodule E V) [FiniteDimensional E (V ⧸ U)]
    (hdim : Module.finrank E (V ⧸ U) ≤ 1) {a : V} (ha : a ∉ U) :
    U ⊔ Submodule.span E {a} = ⊤ := by
  have hq : U.mkQ a ≠ 0 := fun h => ha ((Submodule.Quotient.mk_eq_zero U).mp h)
  have hn : Module.finrank E (V ⧸ U) ≠ 0 := fun h =>
    hq ((finrank_zero_iff_forall_zero.mp h) (U.mkQ a))
  have hd : Module.finrank E (V ⧸ U) = 1 := by omega
  have hg := (finrank_eq_one_iff_of_nonzero' (U.mkQ a) hq).mp hd
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨e, he⟩ := hg (U.mkQ x)
  have hb : x - e • a ∈ U := by
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (x - e • a) = 0
    rw [map_sub, map_smul, he, sub_self]
  exact Submodule.mem_sup.mpr ⟨x - e • a, hb, e • a,
    Submodule.mem_span_singleton.mpr ⟨e, rfl⟩, sub_add_cancel _ _⟩

end GeneralizedEuler.Section2
