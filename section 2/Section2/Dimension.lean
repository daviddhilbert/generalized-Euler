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
@[expose]
def coordinateProjection {k : ℕ} (e : Fin k ↪ Fin n) (x : Fin n → X) : Fin k → X :=
  x ∘ e

def HasInteriorProjection {k : ℕ} (D : Set (Fin n → X)) : Prop :=
  ∃ e : Fin k ↪ Fin n, (interior (coordinateProjection e '' D)).Nonempty

/-- Projection dimension, with zero also used for the empty set. -/
def projectionDimension (D : Set (Fin n → X)) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (fun k => HasInteriorProjection (k := k) D)).sup id

@[expose]
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

theorem projectionDimension_le_iff {D : Set (Fin n → X)} {k : ℕ} :
    projectionDimension D ≤ k ↔
      ∀ (m : Fin (n + 1)) (p : Fin m.val ↪ Fin n), k < m.val →
        ¬(interior (coordinateProjection p '' D)).Nonempty := by
  classical
  constructor
  · intro h m p hm hi
    exact hm.not_ge ((le_projectionDimension ⟨p, hi⟩).trans h)
  · intro h
    apply Finset.sup_le
    intro m hm
    obtain ⟨hn, p, hp⟩ := Finset.mem_filter.mp hm
    exact le_of_not_gt (fun hk => h ⟨m, Finset.mem_range.mp hn⟩ p hk hp)

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

theorem hasInteriorProjection_zero {D : Set (Fin n → X)} (hD : D.Nonempty) :
    HasInteriorProjection (k := 0) D := by
  let e : Fin 0 ↪ Fin n := ⟨Fin.elim0, fun i => i.elim0⟩
  obtain ⟨x, hx⟩ := hD
  refine ⟨e, ?_⟩
  have h : coordinateProjection e '' D = Set.univ :=
    Set.eq_univ_of_forall fun z => ⟨x, hx, Subsingleton.elim _ z⟩
  rw [h, interior_univ]
  exact ⟨Fin.elim0, Set.mem_univ _⟩

theorem hasInteriorProjection_projectionDimension {D : Set (Fin n → X)}
    (hD : D.Nonempty) : HasInteriorProjection (k := projectionDimension D) D := by
  classical
  let s := (Finset.range (n + 1)).filter (fun k => HasInteriorProjection (k := k) D)
  have h0 : 0 ∈ s := Finset.mem_filter.mpr ⟨by simp, hasInteriorProjection_zero hD⟩
  obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup s ⟨0, h0⟩ id
  change projectionDimension D = k at hsup
  rw [hsup]
  exact (Finset.mem_filter.mp hk).2

/-- The largest projection dimension in Definition 2.25 is attained by
a single RV fiber of a nonempty set. -/
theorem exists_nonempty_fiber_projectionDimension_eq_vfDimension {Y : Type*}
    {D : Set ((Fin n → X) × Y)} (hD : D.Nonempty) :
    ∃ y, (sortedFiber D y).Nonempty ∧ projectionDimension (sortedFiber D y) = vfDimension D := by
  classical
  let s := (Finset.range (n + 1)).filter
    (fun k => ∃ y, HasInteriorProjection (k := k) (sortedFiber D y))
  obtain ⟨⟨x, y⟩, hxy⟩ := hD
  have h0 : 0 ∈ s := Finset.mem_filter.mpr
    ⟨by simp, y, hasInteriorProjection_zero ⟨x, hxy⟩⟩
  obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup s ⟨0, h0⟩ id
  change vfDimension D = k at hsup
  obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hk).2
  refine ⟨y, ?_, le_antisymm (projectionDimension_fiber_le_vfDimension D y)
    (hsup.symm ▸ le_projectionDimension hy)⟩
  obtain ⟨e, z, hz⟩ := hy
  obtain ⟨x, hx, _⟩ := interior_subset hz
  exact ⟨x, hx⟩

theorem exists_fiber_projectionDimension_eq_vfDimension {Y : Type*}
    {D : Set ((Fin n → X) × Y)} (hD : D.Nonempty) :
    ∃ y, projectionDimension (sortedFiber D y) = vfDimension D := by
  obtain ⟨y, _, hy⟩ := exists_nonempty_fiber_projectionDimension_eq_vfDimension hD
  exact ⟨y, hy⟩

/-- Apply the approved weakly o-minimal projection-equals-rank result
fiberwise to obtain the algebraic description of VF dimension. -/
theorem vfDimension_eq_max_fiber_rank {Y : Type*}
    {D : Set ((Fin n → X) × Y)} (hD : D.Nonempty) (rank : Y → ℕ)
    (hrank : ∀ y, projectionDimension (sortedFiber D y) = rank y) :
    (∀ y, rank y ≤ vfDimension D) ∧ ∃ y, rank y = vfDimension D := by
  exact ⟨fun y => hrank y ▸ projectionDimension_fiber_le_vfDimension D y,
    Exists.imp (fun y hy => hrank y ▸ hy)
      (exists_fiber_projectionDimension_eq_vfDimension hD)⟩

omit [TopologicalSpace X] in
/-- Coordinate projections that are injective on the fibers of a finite
chart cover give a single injection after tagging the pieces in RV.
Smaller charts are padded with the same named field element. -/
theorem exists_embedding_with_piecewise_projection_graph {Y R : Type*} {k l : ℕ}
    (D : Set ((Fin n → X) × Y)) (pieces : Fin l → Set D)
    (hcover : ∀ x : D, ∃ i, x ∈ pieces i) (m : Fin l → ℕ)
    (hm : ∀ i, m i ≤ k) (projection : ∀ i, Fin (m i) ↪ Fin n)
    (hinjective : ∀ i, Set.InjOn
      (fun x : D => (coordinateProjection (projection i) x.val.1, x.val.2)) (pieces i))
    (padding : X) (tag : Fin l ↪ R) :
    ∃ f : D ↪ (Fin k → X) × (Y × R), ∀ x z,
      f x = z ↔ ∃ i, x ∈ pieces i ∧ (∀ j < i, x ∉ pieces j) ∧
        ((fun j : Fin k => if h : j.val < m i then x.val.1 (projection i ⟨j.val, h⟩)
          else padding), x.val.2, tag i) = z := by
  classical
  let indices (x : D) : Finset (Fin l) := Finset.univ.filter (fun i => x ∈ pieces i)
  have hne (x : D) : (indices x).Nonempty := by
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let piece (x : D) : Fin l := (indices x).min' (hne x)
  have hp (x : D) : x ∈ pieces (piece x) := by
    have h : piece x ∈ indices x := Finset.min'_mem (indices x) (hne x)
    exact (Finset.mem_filter.mp h).2
  have hmin (x : D) (j : Fin l) (hj : x ∈ pieces j) : piece x ≤ j :=
    Finset.min'_le (indices x) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  let coordinates (i : Fin l) (x : D) (j : Fin k) : X :=
    if h : j.val < m i then x.val.1 (projection i ⟨j.val, h⟩) else padding
  let f (x : D) : (Fin k → X) × (Y × R) :=
    ⟨coordinates (piece x) x, x.val.2, tag (piece x)⟩
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro x y hxy
    have hlabel : piece x = piece y := tag.injective (congrArg (fun z => z.2.2) hxy)
    apply hinjective (piece x) (hp x) (hlabel.symm ▸ hp y)
    apply Prod.ext
    · funext j
      let j' : Fin k := Fin.castLE (hm (piece x)) j
      have hcoord := congrFun (congrArg Prod.fst hxy) j'
      change coordinates (piece x) x j' = coordinates (piece y) y j' at hcoord
      rw [← hlabel] at hcoord
      have hj : j'.val < m (piece x) := j.isLt
      have hj' : (⟨j'.val, hj⟩ : Fin (m (piece x))) = j := Fin.ext rfl
      simpa only [coordinates, dite_eq_left hj, hj', coordinateProjection, Function.comp_apply]
        using hcoord
    · exact congrArg (fun z => z.2.1) hxy
  · intro x z
    constructor
    · intro h
      exact ⟨piece x, hp x, fun j hj hjx => (not_lt_of_ge (hmin x j hjx)) hj, h⟩
    · rintro ⟨i, hi, hfirst, h⟩
      have heq : piece x = i := (hmin x i hi).antisymm
        (le_of_not_gt fun hj => hfirst _ hj (hp x))
      change (coordinates (piece x) x, x.val.2, tag (piece x)) = z
      rw [heq]
      exact h

omit [TopologicalSpace X] in
theorem exists_embedding_of_piecewise_projection {Y R : Type*} {k l : ℕ}
    (D : Set ((Fin n → X) × Y)) (pieces : Fin l → Set D)
    (hcover : ∀ x : D, ∃ i, x ∈ pieces i) (m : Fin l → ℕ)
    (hm : ∀ i, m i ≤ k) (projection : ∀ i, Fin (m i) ↪ Fin n)
    (hinjective : ∀ i, Set.InjOn
      (fun x : D => (coordinateProjection (projection i) x.val.1, x.val.2)) (pieces i))
    (padding : X) (tag : Fin l ↪ R) :
    Nonempty (D ↪ (Fin k → X) × (Y × R)) := by
  obtain ⟨f, _⟩ := exists_embedding_with_piecewise_projection_graph D pieces hcover m hm
    projection hinjective padding tag
  exact ⟨f⟩

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
