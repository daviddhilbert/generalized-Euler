module

public import Section2.ProjectionTopology
public import Section2.ResidueClassification
public import Section2.ValueFiberTopology

/-! The coordinate projections of an embedded residue set and of the
original set have interior in exactly the same dimensions. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

/-- The order topology of the residue field. -/
@[instance_reducible]
def residueOrderTopology : TopologicalSpace (Residue O) :=
  letI := residueLinearOrder O hO
  Preorder.topology _

-- Use local instances at the given convex ring, since convexity determines these orders.
variable [Fact (IsOrderConvex O)]

private instance : LinearOrder (Residue O) := residueLinearOrder O Fact.out
private instance : LinearOrder (RV0 O) := rvLinearOrder O Fact.out
private instance : TopologicalSpace (Residue O) := residueOrderTopology O Fact.out
private instance : TopologicalSpace (RV0 O) := rvOrderTopology O Fact.out
private instance : OrderTopology (Residue O) := ⟨rfl⟩
private instance : OrderTopology (RV0 O) := ⟨rfl⟩

private def nonzeroSignRegion {X : Type*} [LinearOrder X] [Zero X] (positive : Bool) : Set X :=
  if positive then Set.Ioi 0 else Set.Iio 0

private theorem nonzeroSignRegion_open {X : Type*} [LinearOrder X] [Zero X]
    [TopologicalSpace X] [OrderTopology X] (b : Bool) : IsOpen (nonzeroSignRegion (X := X) b) := by
  cases b
  · exact isOpen_Iio
  · exact isOpen_Ioi

private theorem nonzeroSignRegion_ordConnected {X : Type*} [LinearOrder X] [Zero X]
    (b : Bool) : Set.OrdConnected (nonzeroSignRegion (X := X) b) := by
  cases b
  · exact Set.ordConnected_Iio
  · exact Set.ordConnected_Ioi

private theorem mem_nonzeroSignRegion_iff (b : Bool) (r : Residue O) :
    residueRV O r ∈ nonzeroSignRegion b ↔ r ∈ nonzeroSignRegion b := by
  have hm := residueRV_strictMono O Fact.out
  cases b
  · change residueRV O r < 0 ↔ r < 0
    rw [← residueRV_zero O]
    exact hm.lt_iff_lt
  · change 0 < residueRV O r ↔ 0 < r
    rw [← residueRV_zero O]
    exact hm.lt_iff_lt

private theorem mem_nonzeroSignRegion_rv_iff (b : Bool) (x : K) :
    rv O x ∈ nonzeroSignRegion b ↔ x ∈ nonzeroSignRegion b := by
  cases b
  · exact rv_lt_zero_iff O Fact.out
  · exact zero_lt_rv_iff O Fact.out

private theorem ne_zero_of_mem_nonzeroSignRegion {X : Type*} [LinearOrder X] [Zero X]
    {b : Bool} {x : X} (hx : x ∈ nonzeroSignRegion b) : x ≠ 0 := by
  cases b
  · exact (show x < 0 from hx).ne
  · exact (show 0 < x from hx).ne'

private theorem exists_nonzeroSignRegion_of_ne_zero {X : Type*} [LinearOrder X] [Zero X]
    {x : X} (hx : x ≠ 0) : ∃ b, x ∈ nonzeroSignRegion b := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

private theorem range_residueRV_nonzeroSignRegion (b : Bool) :
    Set.range (fun x : nonzeroSignRegion (X := Residue O) b => residueRV O x.val) =
      nonzeroSignRegion b ∩ unsignedValue O ⁻¹' {1} := by
  ext t
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(mem_nonzeroSignRegion_iff O b r).mpr r.property,
      unsignedValue_residueRV_of_ne_zero O (ne_zero_of_mem_nonzeroSignRegion r.property)⟩
  · rintro ⟨ht, hv⟩
    have hrange : t ∈ Set.range (residueRV O) := by
      rw [range_residueRV]
      exact Or.inr hv
    obtain ⟨r, rfl⟩ := hrange
    exact ⟨⟨r, (mem_nonzeroSignRegion_iff O b r).mp ht⟩, rfl⟩

private theorem unitValue_signRegion_ordConnected (b : Bool) :
    Set.OrdConnected (nonzeroSignRegion b ∩ unsignedValue O ⁻¹' {1}) := by
  constructor
  intro x hx y hy t ht
  refine ⟨(nonzeroSignRegion_ordConnected b).out hx.1 hy.1 ht, ?_⟩
  obtain ⟨a, rfl⟩ := rv_surjective O x
  obtain ⟨c, rfl⟩ := rv_surjective O y
  obtain ⟨d, rfl⟩ := rv_surjective O t
  have ha := (mem_nonzeroSignRegion_rv_iff O b a).mp hx.1
  have hc := (mem_nonzeroSignRegion_rv_iff O b c).mp hy.1
  have hd := (mem_nonzeroSignRegion_rv_iff O b d).mp
    ((nonzeroSignRegion_ordConnected b).out hx.1 hy.1 ht)
  have hav : O.valuation a = 1 := (unsignedValue_rv O a).symm.trans hx.2
  have hcv : O.valuation c = 1 := (unsignedValue_rv O c).symm.trans hy.2
  change unsignedValue O (rv O d) = 1
  rw [unsignedValue_rv]
  rcases (rv_le_rv_iff O Fact.out).mp ht.1 with had | he
  · rcases (rv_le_rv_iff O Fact.out).mp ht.2 with hdc | he
    · cases b
      · have hca : O.valuation c ≤ O.valuation d := by
          simpa only [O.valuation.map_neg] using
            valuation_le_of_nonneg_le O Fact.out (neg_nonneg.mpr (show c < 0 from hc).le)
              (neg_le_neg hdc)
        have hda : O.valuation d ≤ O.valuation a := by
          simpa only [O.valuation.map_neg] using
            valuation_le_of_nonneg_le O Fact.out (neg_nonneg.mpr (show d < 0 from hd).le)
              (neg_le_neg had)
        exact (hda.trans_eq hav).antisymm (hcv ▸ hca)
      · have hda := valuation_le_of_nonneg_le O Fact.out (show 0 < a from ha).le had
        have hdc' := valuation_le_of_nonneg_le O Fact.out (show 0 < d from hd).le hdc
        exact (hdc'.trans_eq hcv).antisymm (hav ▸ hda)
    · exact (unsignedValue_rv O d).symm.trans
        ((congrArg (unsignedValue O) he).trans hy.2)
  · exact (unsignedValue_rv O d).symm.trans
      ((congrArg (unsignedValue O) he.symm).trans hx.2)

private theorem residueRV_signed_isOpenEmbedding (b : Bool) :
    IsOpenEmbedding (fun x : nonzeroSignRegion (X := Residue O) b => residueRV O x.val) := by
  let := nonzeroSignRegion_ordConnected (X := Residue O) b
  have hm : StrictMono (fun x : nonzeroSignRegion (X := Residue O) b => residueRV O x.val) :=
    fun _ _ h => residueRV_strictMono O Fact.out h
  refine ⟨hm.isEmbedding_of_ordConnected ?_, ?_⟩
  · rw [range_residueRV_nonzeroSignRegion O]
    exact unitValue_signRegion_ordConnected O b
  · rw [range_residueRV_nonzeroSignRegion O]
    exact (nonzeroSignRegion_open b).inter (unsignedValue_fiber_isOpen O Fact.out one_ne_zero)

private theorem dense_compl_point_of_between {X : Type*} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] {p : X} (hl : ∃ l, l < p) (hu : ∃ u, p < u)
    (hBetween : ∀ u, p < u → ∃ x, p < x ∧ x < u) : Dense ({p}ᶜ : Set X) := by
  rw [dense_compl_singleton_iff_not_open]
  intro ho
  obtain ⟨l, u, hp, hI⟩ := (mem_nhds_iff_exists_Ioo_subset' hl hu).mp
    (ho.mem_nhds (Set.mem_singleton p))
  obtain ⟨x, hpx, hxu⟩ := hBetween u hp.2
  exact hpx.ne' (Set.mem_singleton_iff.mp (hI ⟨hp.1.trans hpx, hxu⟩))

private theorem dense_residue_nonzero : Dense ({0}ᶜ : Set (Residue O)) := by
  let := residue_isOrderedRing O Fact.out
  exact dense_compl_point_of_between ⟨-1, neg_one_lt_zero⟩ ⟨1, zero_lt_one⟩
    (fun u hu => exists_between hu)

private theorem dense_rv_nonzero : Dense ({0}ᶜ : Set (RV0 O)) := by
  refine dense_compl_point_of_between
    ⟨rv O (-1), (rv_lt_zero_iff O Fact.out).mpr neg_one_lt_zero⟩
    ⟨rv O 1, (zero_lt_rv_iff O Fact.out).mpr zero_lt_one⟩ ?_
  intro t ht
  obtain ⟨x, rfl⟩ := rv_surjective O t
  have hx := (zero_lt_rv_iff O Fact.out).mp ht
  refine ⟨rv O (x / 2), (zero_lt_rv_iff O Fact.out).mpr (div_pos hx zero_lt_two),
    (rv_lt_rv_iff O Fact.out).mpr ⟨div_lt_self hx one_lt_two, ?_⟩⟩
  intro he
  have h := (rv_eq_rv_iff_valuation O (div_pos hx zero_lt_two).ne').mp he.symm
  rw [sub_half] at h
  exact (lt_irrefl _) h

set_option linter.style.haveILetI false in
omit [Fact (IsOrderConvex O)] in
/-- Embedding residue tuples into RV preserves projection dimension in
the canonical orders. The positive and negative residue branches are
open in RV, and a full-dimensional open projection meets the product
of the complements of zero. -/
theorem embeddedResidueSet_projectionDimension {I : Type} [Finite I] (R : Set (I → Residue O)) :
    letI := residueOrderTopology O hO
    letI := rvOrderTopology O hO
    finiteTupleProjectionDimension (embeddedResidueSet O R) = finiteTupleProjectionDimension R := by
  letI : Fact (IsOrderConvex O) := ⟨hO⟩
  letI := residueOrderTopology O hO
  letI := rvOrderTopology O hO
  rw [embeddedResidueSet_eq_image]
  have hu : (⋃ b, nonzeroSignRegion (X := Residue O) b) = {0}ᶜ := by
    ext r
    constructor
    · intro hr
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hr
      exact ne_zero_of_mem_nonzeroSignRegion hb
    · intro hr
      exact Set.mem_iUnion.mpr (exists_nonzeroSignRegion_of_ne_zero hr)
  have hd : Dense (⋃ b, nonzeroSignRegion (X := Residue O) b) :=
    hu.symm ▸ dense_residue_nonzero O
  refine finiteTupleProjectionDimension_image_of_dense_regions (residueRV O)
    (residueRV_injective O) (nonzeroSignRegion (X := Residue O)) R
    nonzeroSignRegion_open (residueRV_signed_isOpenEmbedding O) hd (dense_rv_nonzero O) ?_
  intro r hr
  apply exists_nonzeroSignRegion_of_ne_zero
  intro he
  apply hr
  rw [he, residueRV_zero]
  exact Set.mem_singleton _

end GeneralizedEuler.Section2
