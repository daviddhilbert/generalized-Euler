module

public import Section3.DifferentialPolynomial
public import Section3.DefinableContraction
public import Section3.DefinableFunctions
import all Section3.Contraction

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set Filter
open scoped Topology

/-- A field locus of empty interior misses a point on each open fiber
which it meets. Thus its entire image is accounted for by 3.26. -/
theorem image_eq_boundary_of_open_fibers {X U : Type*} [TopologicalSpace X]
    (p : X → U) (H : Set X) (empty : interior H = ∅)
    (openFibers : ∀ x ∈ H, ∀ᶠ y in 𝓝 x, p y = p x) : p '' H = rvBoundary p H := by
  ext u
  refine ⟨?_,fun h => h.1⟩
  rintro ⟨x,hx,rfl⟩
  refine ⟨mem_image_of_mem p hx,?_⟩
  by_contra! allIn
  have inside : x ∈ interior H := mem_interior_iff_mem_nhds.mpr ((openFibers x hx).mono (fun y hy => allIn y hy))
  simp only [empty,notMem_empty] at inside

/-- The required open fibers are automatic on nonzero RV-polydiscs.
At a nonsmooth point of the unit domain the ordinary field topology
therefore suffices for applying the boundary theorem. -/
theorem rv_image_nonsmooth_eq_boundary {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K] (O : ValuationSubring K) (hO : IsOrderConvex O)
    {e : K} (pos : 0 < e) (small : O.valuation e < 1) {n : ℕ} (H : Set (Fin n → K))
    (nz : ∀ x ∈ H, ∀ j, x j ≠ 0) (empty : interior H = ∅) :
    (fun x => (rv O) ∘ x) '' H = rvBoundary (fun x => rv O ∘ x) H := by
  apply image_eq_boundary_of_open_fibers _ H empty
  intro x hx
  have each (j : Fin n) : ∀ᶠ y in 𝓝 x, rv O (y j) = rv O (x j) :=
    (continuous_apply j).continuousAt.tendsto.eventually (eventually_rv_eq O hO pos small (nz x hx j))
  exact (Filter.eventually_all.mpr each).mono (fun _ h => funext h)

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [TopologicalSpace k] [OrderTopology k]
  {n : ℕ} {L : Language} [L.Structure k] {P : Set k}

/-- Construction of the initial open domain in 3.32. The field
nonsmooth set uses 3.26, the partials use 3.28, and the residue charts
use o-minimal generic smoothness. Their exceptional labels and the
boundary of the original domain have lower dimension in every arity. -/
theorem open_smooth_contraction_domain {X I : Type*} [TopologicalSpace X] [Finite I]
    (F : OrderedFieldTerms L) (hF : InterpretsOrderedFieldTerms (A := k) F)
    (p : X → Fin n → k) (A : Set (Fin n → k)) (dA : P.Definable L A)
    (H : Set X) (nonsmooth : interior H = ∅) (fib : ∀ x ∈ H, ∀ᶠ y in 𝓝 x, p y = p x)
    (dB : P.Definable L (rvBoundary p H)) (bd : projectionDimensionWithBot (rvBoundary p H) < (n : WithBot ℕ))
    (E : I → Set (Fin n → k))
    (data : ∀ i, P.Definable L (E i) ∧ projectionDimensionWithBot (E i) < (n : WithBot ℕ))
    (tame : ∀ B : Set (Fin n → k), P.Definable L B → interior B = ∅ → IsNowhereDense B)
    (front : IsNowhereDense (frontier A)) :
    ∃ W ⊆ A, P.Definable L W ∧ IsOpen W ∧ P.Definable L (A \ W) ∧
      projectionDimensionWithBot (A \ W) < (n : WithBot ℕ) ∧
      (∀ x, p x ∈ W → x ∉ H) ∧ ∀ i, Disjoint W (E i) := by
  let B := rvBoundary p H ∪ ⋃ i, E i
  have db : P.Definable L B := dB.union (definable_iUnion_of_finite (fun i => (data i).1))
  have thin : IsNowhereDense B := (tame _ dB (dimensionWithBot_lt_arity_iff.mp bd)).union
    (IsNowhereDense.iUnion (fun i => tame _ (data i).1 (dimensionWithBot_lt_arity_iff.mp (data i).2)))
  let W := interior (A \ B)
  have dW : P.Definable L W := definable_fiber_interior F hF (fun _ y => y ∈ A \ B) ((dA.sdiff db).preimage_comp Sum.inr)
  have bad : A \ W ⊆ frontier A ∪ closure B := by
    intro x hx
    by_contra! no
    have ax := (mem_interior_iff_notMem_frontier hx.1).mpr (fun h => no (Or.inl h))
    have bx : x ∈ interior Bᶜ := by rw [interior_compl]; exact fun h => no (Or.inr h)
    exact hx.2 (by change x ∈ interior (A ∩ Bᶜ); rw [interior_inter]; exact ⟨ax,bx⟩)
  have thinBad := (front.union (show IsNowhereDense (closure B) by simpa [IsNowhereDense] using thin)).mono bad
  refine ⟨W,fun _ h => (interior_subset h).1,dW,isOpen_interior,dA.sdiff dW,
    dimensionWithBot_lt_arity_iff.mpr (eq_empty_of_subset_empty ((interior_mono subset_closure).trans thinBad.subset)),?_,?_⟩
  · intro x hx h
    apply (interior_subset hx).2
    exact Or.inl ((image_eq_boundary_of_open_fibers p H nonsmooth fib) ▸ mem_image_of_mem p h)
  · intro i
    exact disjoint_left.mpr (fun x hx he => (interior_subset hx).2 (Or.inr (mem_iUnion_of_mem i he)))

end GeneralizedEuler.Section3
