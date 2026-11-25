module

public import Section3.BoundaryInduction
public import Mathlib.Topology.GDelta.Basic

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {R K : Type*} {n : ℕ} [TopologicalSpace R]

private def separateCoordinate (i : Fin (n+1)) :
    (Fin (n+1) → R) ≃ₜ (Fin n → R) × R where
  toFun x := (i.removeNth x,x i)
  invFun x := i.insertNth x.2 x.1
  left_inv := Fin.insertNth_self_removeNth i
  right_inv x := by simp
  continuous_toFun := (continuous_pi fun j => continuous_apply (i.succAbove j)).prodMk (continuous_apply i)
  continuous_invFun := Continuous.finInsertNth (A := fun _ => R) i continuous_snd continuous_fst

/-- Forgetting a coordinate pulls a nowhere dense base up to a nowhere
dense cylinder, including when the base has arity zero. -/
theorem nowhereDense_coordinate_cylinder (i : Fin (n+1)) {B : Set (Fin n → R)}
    (hB : IsNowhereDense B) : IsNowhereDense ((fun x : Fin (n+1) → R => i.removeNth x) ⁻¹' B) := by
  let e := separateCoordinate (R := R) i
  have ho : IsOpenMap (fun x : Fin (n+1) → R => i.removeNth x) :=
    isOpenMap_fst.comp e.isOpenMap
  have hc : Continuous (fun x : Fin (n+1) → R => i.removeNth x) :=
    continuous_fst.comp e.continuous
  exact eq_empty_of_subset_empty (((interior_mono (hc.closure_preimage_subset B)).trans
    ho.interior_preimage_subset_preimage_interior).trans (by rw [show interior (closure B) = ∅ from hB]; rfl))

variable [LinearOrder R] [DenselyOrdered R] [NoMinOrder R] [NoMaxOrder R] [OrderTopology R]

/-- A finite family of descended graphs omits points in every open box,
even when the functions are discontinuous. -/
theorem empty_interior_coordinate_graphs {I : Type*} [Finite I] (i : Fin (n+1))
    (g : I → (Fin n → R) → R) :
    interior {x : Fin (n+1) → R | ∃ k, x i = g k (i.removeNth x)} = ∅ := by
  let e := separateCoordinate (R := R) i
  let B : Set ((Fin n → R) × R) := {x | ∃ k, x.2 = g k x.1}
  have h := empty_interior_of_finite_last_fibers (A := B) (fun a =>
    (finite_range (fun k => g k a)).subset (fun _ ⟨k,hk⟩ => ⟨k,hk.symm⟩))
  change interior (e ⁻¹' B) = ∅
  rw [←e.preimage_interior,h,preimage_empty]

/-- The successor step of 3.26. The auxiliary dimension-theory input
from 2.27 says that the definable finite unions of graphs used here are
nowhere dense as soon as they have empty interior. -/
theorem boundary_dimension_step {I J : Type*} [Finite I] [Finite J] (p : K → R)
    (A : Set (Fin (n+1) → K))
    (domain : Fin (n+1) → I → Set (Fin n → K))
    (branch : Fin (n+1) → I → J → (Fin n → K) → R)
    (graph : Fin (n+1) → I → J → (Fin n → R) → R)
    (enum : ∀ i (a : Fin n → K) t, t ∈ rvBoundary p {v | i.insertNth v a ∈ A} →
      ∃ j, a ∈ domain i j ∧ ∃ k, t = branch i j k a)
    (descend : ∀ i j k a, a ∈ domain i j →
      (p ∘ a) ∈ rvInterior (fun b => p ∘ b) (domain i j) →
      branch i j k a = graph i j k (p ∘ a))
    (lower : ∀ i j, IsNowhereDense (rvBoundary (fun a => p ∘ a) (domain i j)))
    (tame : ∀ i, let G := {x : Fin (n+1) → R | ∃ jk : I × J, x i = graph i jk.1 jk.2 (i.removeNth x)}
      interior G = ∅ → IsNowhereDense G) :
    IsNowhereDense (rvBoundary (fun x => p ∘ x) A) ∧
      projectionDimensionWithBot (rvBoundary (fun x => p ∘ x) A) < ((n+1 : ℕ) : WithBot ℕ) := by
  let B (i : Fin (n+1)) := ⋃ j, (fun x : Fin (n+1) → R => i.removeNth x) ⁻¹' rvBoundary (fun x => p ∘ x) (domain i j)
  let G (i : Fin (n+1)) := {x : Fin (n+1) → R | ∃ q : I × J, x i = graph i q.1 q.2 (i.removeNth x)}
  have hB i : IsNowhereDense (B i) :=
    IsNowhereDense.iUnion fun j => nowhereDense_coordinate_cylinder i (lower _ j)
  have hG i : IsNowhereDense (G i) := tame i (empty_interior_coordinate_graphs i _)
  have cover : rvBoundary (fun x => p ∘ x) A ⊆ ⋃ i, B i ∪ G i := by
    intro x hx
    obtain ⟨i,j,hj⟩ := boundary_subset_charts p A domain branch graph enum descend hx
    apply mem_iUnion_of_mem i
    rcases hj with hb | ⟨_,k,hk⟩
    · exact Or.inl (mem_iUnion_of_mem j hb)
    · exact Or.inr ⟨(j,k),hk⟩
  have thin := (IsNowhereDense.iUnion fun i => (hB i).union (hG i)).mono cover
  exact ⟨thin,dimensionWithBot_lt_arity_iff.mpr
    (eq_empty_of_subset_empty ((interior_mono subset_closure).trans thin.subset))⟩

end GeneralizedEuler.Section3
