module

public import Section2.LeadingTermOrder
public import Section2.ValueSplitting

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

end GeneralizedEuler.Section2
