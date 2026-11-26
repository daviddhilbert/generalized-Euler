module

public import Section4.QuotientSpanProfiles
public import Mathlib.Order.Minimal

/-! Computing quotient ranks from the surviving factors of a padded box,
and recovering maximal box types from tuples attaining those ranks. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem quotientTupleSpan_restrict {ι : Type*} (G : Submodule F V) (x : ι → V)
    (large : Set ι) (vanish : ∀ i, i ∉ large → x i ∈ G) :
    quotientTupleSpan G x = quotientTupleSpan G (fun i : large => x i.val) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases h : i ∈ large
    · exact Submodule.subset_span ⟨⟨i,h⟩,rfl⟩
    · change G.mkQ (x i) ∈ _
      rw [show G.mkQ (x i) = 0 from (Submodule.Quotient.mk_eq_zero G).mpr (vanish i h)]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨i.val,rfl⟩

theorem box_rank_bound {ι : Type*} (G : Submodule F V) (x : ι → V)
    (large : Set ι) [Fintype large] (vanish : ∀ i, i ∉ large → x i ∈ G) :
    Module.finrank F (quotientTupleSpan G x) ≤ Fintype.card large := by
  rw [quotientTupleSpan_restrict G x large vanish]
  exact finrank_range_le_card _

theorem box_rank_attained {ι : Type*} (G : Submodule F V) (x : ι → V)
    (large : Set ι) [Fintype large] (vanish : ∀ i, i ∉ large → x i ∈ G)
    (ind : LinearIndependent F (fun i : large => G.mkQ (x i.val))) :
    Module.finrank F (quotientTupleSpan G x) = Fintype.card large := by
  rw [quotientTupleSpan_restrict G x large vanish]
  exact finrank_span_eq_card ind

/-- Mutual domination identifies maximal elements even when the witness
for one comparison need not be the witness for the reverse comparison. -/
theorem maximal_profiles_of_domination {P : Type*} [PartialOrder P] {X Y : Set P}
    (forward : ∀ x ∈ X, ∃ y ∈ Y, x ≤ y) (back : ∀ y ∈ Y, ∃ x ∈ X, y ≤ x) :
    {p | Maximal (· ∈ X) p} = {p | Maximal (· ∈ Y) p} := by
  have one {U W : Set P} (fwd : ∀ x ∈ U, ∃ y ∈ W, x ≤ y)
      (rev : ∀ y ∈ W, ∃ x ∈ U, y ≤ x) {p : P} (h : Maximal (· ∈ U) p) :
      Maximal (· ∈ W) p := by
    obtain ⟨q,hq,hpq⟩ := fwd p h.1
    obtain ⟨r,hr,hqr⟩ := rev q hq
    have hrp := h.2 hr (hpq.trans hqr)
    have eq := le_antisymm hpq (hqr.trans hrp)
    refine ⟨eq ▸ hq, ?_⟩
    intro t ht hpt
    obtain ⟨r,hr,htr⟩ := rev t ht
    exact htr.trans (h.2 hr (hpt.trans htr))
  exact Set.ext fun _ => ⟨one forward back, one back forward⟩

/-- A common space of attainable tuple profiles determines the maximal
box ranks if every box has a point attaining all its bounds at once. -/
theorem maximal_box_ranks {P I J : Type*} [PartialOrder P] (r : I → P) (s : J → P)
    {X : I → Set P} {Y : J → Set P}
    (boundX : ∀ i p, p ∈ X i → p ≤ r i) (boundY : ∀ j p, p ∈ Y j → p ≤ s j)
    (attainX : ∀ i, r i ∈ X i) (attainY : ∀ j, s j ∈ Y j)
    (eq : (⋃ i, X i) = ⋃ j, Y j) :
    {p | Maximal (· ∈ Set.range r) p} = {p | Maximal (· ∈ Set.range s) p} := by
  apply maximal_profiles_of_domination
  · rintro _ ⟨i,rfl⟩
    obtain ⟨j,h⟩ := Set.mem_iUnion.mp (eq ▸ Set.mem_iUnion.mpr ⟨i,attainX i⟩)
    exact ⟨_,⟨j,rfl⟩,boundY j _ h⟩
  · rintro _ ⟨j,rfl⟩
    obtain ⟨i,h⟩ := Set.mem_iUnion.mp (eq.symm ▸ Set.mem_iUnion.mpr ⟨j,attainY j⟩)
    exact ⟨_,⟨i,rfl⟩,boundX i _ h⟩

end GeneralizedEuler.Section4
