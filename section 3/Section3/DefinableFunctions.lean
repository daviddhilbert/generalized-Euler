module

public import Section3.TopTerms
public import Section2.DiscCodes
public import Mathlib.Topology.Order.DenselyOrdered

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set Filter
open scoped Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [OrderTopology K] (O : ValuationSubring K)

/-- A nonzero leading term is locally constant for the order topology.
An element of the maximal ideal gives an explicit interval inside its fiber. -/
theorem eventually_rv_eq (hO : IsOrderConvex O) {e : K} (he : 0 < e)
    (heO : O.valuation e < 1) {y : K} (hy : y ≠ 0) :
    ∀ᶠ z in 𝓝 y, rv O z = rv O y := by
  let d := e * |y|
  have hd : 0 < d := mul_pos he (abs_pos.mpr hy)
  have hdv : O.valuation d < O.valuation y := by
    change O.valuation (e * |y|) < _
    rw [map_mul, valuation_abs]
    simpa using mul_lt_mul_of_pos_right heO (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hy))
  filter_upwards [Ioo_mem_nhds (sub_lt_self y hd) (lt_add_of_pos_right y hd)] with z hz
  have hzd : |z - y| ≤ d := (abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  apply (rv_eq_rv_iff_valuation O hy).mpr
  exact (valuation_le_of_abs_le_abs O hO (by rwa [abs_of_pos hd])).trans_lt hdv

/-- The bad set for one unary field term in 3.3. -/
def criticalSet (g : K → K) : Set K :=
  {y | ¬ ContinuousAt g y} ∪ frontier (g ⁻¹' {0})

theorem eventually_rv_comp_eq (hO : IsOrderConvex O) {e : K} (he : 0 < e)
    (heO : O.valuation e < 1) (g : K → K) {y : K} (hy : y ∉ criticalSet g) :
    ∀ᶠ z in 𝓝 y, rv O (g z) = rv O (g y) := by
  have hc : ContinuousAt g y := not_not.mp (fun h => hy (Or.inl h))
  by_cases hz : g y = 0
  · have hm : y ∈ g ⁻¹' ({0} : Set K) := hz
    have hi : y ∈ interior (g ⁻¹' ({0} : Set K)) := by
      by_contra hn
      exact hy (Or.inr ((mem_frontier_iff_notMem_interior hm).mpr hn))
    filter_upwards [mem_interior_iff_mem_nhds.mp hi] with z h
    rw [show g z = 0 from h, hz]
  · exact hc.tendsto.eventually (eventually_rv_eq O hO he heO hz)

/-- Uniform in all auxiliary inputs. Off the field-definable finite
critical fibers the graph would contain an interval in its output coordinate. -/
theorem graph_output_mem_critical {X T I : Type*} [Finite I]
    (hO : IsOrderConvex O) {e : K} (he : 0 < e) (heO : O.valuation e < 1)
    (f : X → T → K) (g : I → X → K → K)
    (graph : ∀ x t y, (∀ i, rv O (g i x y) = rv O (g i x (f x t))) → y = f x t)
    (x : X) (t : T) : f x t ∈ ⋃ i, criticalSet (g i x) := by
  by_contra hout
  have hloc (i : I) := eventually_rv_comp_eq O hO he heO (g i x)
    (fun hi => hout (Set.mem_iUnion.mpr ⟨i, hi⟩))
  have hall := Filter.eventually_all.mpr hloc
  have heq : ∀ᶠ y in 𝓝 (f x t), y = f x t := hall.mono (fun y hy => graph x t y hy)
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp heq
  obtain ⟨y, hfy, hyr⟩ := exists_between hr
  exact hfy.ne' (hsub ⟨hl.trans hfy, hyr⟩)

/-- Corollary 3.7, using o-minimal finiteness of the critical sets of the
field terms. Taking a field input x gives the relative fiber version. -/
theorem finite_rv_to_field_image {X T I : Type*} [Finite I]
    (hO : IsOrderConvex O) {e : K} (he : 0 < e) (heO : O.valuation e < 1)
    (f : X → T → K) (g : I → X → K → K)
    (graph : ∀ x t y, (∀ i, rv O (g i x y) = rv O (g i x (f x t))) → y = f x t)
    (hfin : ∀ i x, (criticalSet (g i x)).Finite) (x : X) : (Set.range (f x)).Finite := by
  apply (Set.finite_iUnion (fun i => hfin i x)).subset
  rintro _ ⟨t, rfl⟩
  exact graph_output_mem_critical O hO he heO f g graph x t

end GeneralizedEuler.Section3
