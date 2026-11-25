module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Finset.Lattice.Fold

/-! Topological dimensions used in §2.4 and the chart argument for
cutting by a value fiber. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- A coordinate projection indexed by an injection of coordinate sets. -/
def coordinateProjection {k : ℕ} (e : Fin k ↪ Fin n) (x : Fin n → X) : Fin k → X :=
  x ∘ e

def HasInteriorProjection {k : ℕ} (D : Set (Fin n → X)) : Prop :=
  ∃ e : Fin k ↪ Fin n, (interior (coordinateProjection e '' D)).Nonempty

/-- Projection dimension, with zero also used for the empty set. -/
def projectionDimension (D : Set (Fin n → X)) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (fun k => HasInteriorProjection (k := k) D)).sup id

def sortedFiber {Y : Type*} (D : Set ((Fin n → X) × Y)) (y : Y) : Set (Fin n → X) :=
  {x | (x, y) ∈ D}

/-- VF dimension from Definition 2.25, obtained by projecting within a fixed
RV fiber. The finite search is bounded by the number of VF coordinates. -/
def vfDimension {Y : Type*} (D : Set ((Fin n → X) × Y)) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter
    (fun k => ∃ y, HasInteriorProjection (k := k) (sortedFiber D y))).sup id

theorem le_projectionDimension {D : Set (Fin n → X)} {k : ℕ}
    (h : HasInteriorProjection (k := k) D) :
    k ≤ projectionDimension D := by
  classical
  obtain ⟨e, he⟩ := h
  have hk : k ≤ n := by simpa using Fintype.card_le_of_injective e e.injective
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), e, he⟩)

theorem projectionDimension_mono {D B : Set (Fin n → X)} (h : D ⊆ B) :
    projectionDimension D ≤ projectionDimension B := by
  classical
  apply Finset.sup_le
  intro k hk
  obtain ⟨_, e, he⟩ := Finset.mem_filter.mp hk
  exact le_projectionDimension
    ⟨e, he.mono (interior_mono (Set.image_mono h))⟩

theorem projectionDimension_fiber_le_vfDimension {Y : Type*}
    (D : Set ((Fin n → X) × Y)) (y : Y) :
    projectionDimension (sortedFiber D y) ≤ vfDimension D := by
  classical
  apply Finset.sup_le
  intro k hk
  obtain ⟨hk, hf⟩ := Finset.mem_filter.mp hk
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hk, y, hf⟩)

/-- A continuous parametrization of a coordinate chart meets a single
open value fiber on a nonempty open part of its parameter domain.
This is the topological step in the proof of Lemma 2.28. -/
theorem fiber_hasInteriorProjection_of_chart {G : Type*} {k : ℕ}
    (D : Set (Fin n → X)) (value : (Fin n → X) → G)
    (hopen : ∀ x ∈ D, IsOpen (value ⁻¹' {value x}))
    (e : Fin k ↪ Fin n) (U : Set (Fin k → X)) (hU : IsOpen U) (hne : U.Nonempty)
    (chart : (Fin k → X) → (Fin n → X)) (hc : ContinuousOn chart U)
    (hchart : Set.MapsTo chart U D)
    (hproj : ∀ u ∈ U, coordinateProjection e (chart u) = u) :
    ∃ γ ∈ value '' D,
      HasInteriorProjection (k := k) (D ∩ value ⁻¹' {γ}) := by
  obtain ⟨u, hu⟩ := hne
  let γ := value (chart u)
  refine ⟨γ, ⟨chart u, hchart hu, rfl⟩, e, ?_⟩
  have hneigh : (chart ⁻¹' (value ⁻¹' {γ})) ∩ U ∈ nhds u := by
    have hv := (hopen (chart u) (hchart hu)).mem_nhds
      (show chart u ∈ value ⁻¹' {γ} from rfl)
    have hf := hc.continuousAt (hU.mem_nhds hu)
    exact Filter.inter_mem (hf.preimage_mem_nhds hv) (hU.mem_nhds hu)
  refine ⟨u, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hneigh ?_)⟩
  rintro a ⟨ha, haU⟩
  exact ⟨chart a, ⟨hchart haU, ha⟩, hproj a haU⟩

end GeneralizedEuler.Section2
