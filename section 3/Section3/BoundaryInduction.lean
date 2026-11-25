module

public import Section3.ExceptionalLabels
public import Mathlib.Topology.Order.DenselyOrdered

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2
variable {K R : Type*} {n : ℕ}

/-- Switch one coordinate at a time between two points of a rectangular
fiber. Some switch crosses A. This also excludes boundary in arity zero. -/
theorem exists_cut_coordinate (A : Set (Fin n → K)) {x y : Fin n → K}
    (hx : x ∈ A) (hy : y ∉ A) :
    ∃ (i : Fin n) (z w : Fin n → K), z ∈ A ∧ w ∉ A ∧
      (∀ j, z j = x j ∨ z j = y j) ∧ (∀ j, w j = x j ∨ w j = y j) ∧
      ∀ j, j ≠ i → z j = w j := by
  classical
  let path (k : ℕ) (j : Fin n) := if j.val < k then y j else x j
  have h₀ : path 0 ∈ A := by simpa [path] using hx
  have hend : path n ∉ A := by simpa [path] using hy
  have step : ∃ k < n, path k ∈ A ∧ path (k+1) ∉ A := by
    by_contra! no
    have h : ∀ k ≤ n, path k ∈ A := by
      intro k
      induction k with
      | zero => exact fun _ => h₀
      | succ k ih => intro hkn; exact no k (by omega) (ih (by omega))
    exact hend (h n le_rfl)
  obtain ⟨k,hk,hz,hw⟩ := step
  have coord (m : ℕ) (j : Fin n) : path m j = x j ∨ path m j = y j := by
    unfold path
    split <;> simp
  refine ⟨⟨k,hk⟩,path k,path (k+1),hz,hw,coord k,coord (k+1),?_⟩
  intro j hj
  have hne : j.val ≠ k := fun h => hj (Fin.ext h)
  by_cases h : j.val < k
  · simp [path,h,show j.val < k+1 by omega]
  · simp [path,h,show ¬ j.val < k+1 by omega]

/-- The labels of the mixed fiber in 3.26 are already seen in one of
its coordinate sections, with the remaining field coordinates fixed. -/
theorem boundary_witness_in_coordinate_slice (p : K → R) (A : Set (Fin n → K))
    {u : Fin n → R} (hu : u ∈ rvBoundary (fun x => p ∘ x) A) :
    ∃ (i : Fin n) (z w : Fin n → K), z ∈ A ∧ w ∉ A ∧ p ∘ z = u ∧ p ∘ w = u ∧
      ∀ j, j ≠ i → z j = w j := by
  obtain ⟨⟨x,hx,hxu⟩,y,hyu,hy⟩ := hu
  obtain ⟨i,z,w,hz,hw,hzx,hwx,hzw⟩ := exists_cut_coordinate A hx hy
  have lift (s : Fin n → K) (h : ∀ j, s j = x j ∨ s j = y j) : p ∘ s = u := by
    funext j
    exact (h j).elim (fun he => (congrArg p he).trans (congrFun hxu j))
      (fun he => (congrArg p he).trans (congrFun hyu j))
  exact ⟨i,z,w,hz,hw,lift _ hzx,lift _ hwx,hzw⟩

/-- The covering inclusion in the induction of Lemma 3.26. On each chart
the unary boundary labels are enumerated by the given branches. Over a
full base fiber their labels descend to the displayed graphs. -/
theorem boundary_subset_charts {I J : Type*} (p : K → R)
    (A : Set (Fin (n+1) → K))
    (domain : Fin (n+1) → I → Set (Fin n → K))
    (branch : Fin (n+1) → I → J → (Fin n → K) → R)
    (graph : Fin (n+1) → I → J → (Fin n → R) → R)
    (enum : ∀ i (a : Fin n → K) t,
      t ∈ rvBoundary p {v | i.insertNth v a ∈ A} →
      ∃ j, a ∈ domain i j ∧ ∃ k, t = branch i j k a)
    (descend : ∀ i j k a, a ∈ domain i j →
      (p ∘ a) ∈ rvInterior (fun b => p ∘ b) (domain i j) →
      branch i j k a = graph i j k (p ∘ a))
    {t : Fin (n+1) → R} (ht : t ∈ rvBoundary (fun a => p ∘ a) A) :
    ∃ i j, i.removeNth t ∈ rvBoundary (fun a => p ∘ a) (domain i j) ∨
      (i.removeNth t ∈ rvInterior (fun a => p ∘ a) (domain i j) ∧
        ∃ k, t i = graph i j k (i.removeNth t)) := by
  obtain ⟨i,z,w,hz,hw,hzt,hwt,hsame⟩ := boundary_witness_in_coordinate_slice p A ht
  let a := i.removeNth z
  have hwa : a = i.removeNth w := funext fun j =>
    hsame _ (i.succAbove_ne j)
  have hp : p ∘ a = i.removeNth t := funext fun j => congrFun hzt (i.succAbove j)
  have hc : t i ∈ rvBoundary p {v | i.insertNth v a ∈ A} := by
    refine ⟨⟨z i,?_,congrFun hzt i⟩,w i,congrFun hwt i,?_⟩
    · simpa only [a, Set.mem_ofPred_eq, Fin.insertNth_self_removeNth] using hz
    · simpa only [Set.mem_ofPred_eq,hwa,Fin.insertNth_self_removeNth] using hw
  obtain ⟨j,hj,k,hk⟩ := enum i a _ hc
  have him : p ∘ a ∈ (fun b => p ∘ b) '' domain i j := mem_image_of_mem _ hj
  rw [image_eq_interior_union_boundary] at him
  refine ⟨i,j,?_⟩
  rw [←hp]
  exact him.elim (fun h => Or.inr ⟨h,k,hk.trans (descend _ _ _ _ hj h)⟩) Or.inl

/-- A finite last-coordinate fiber cannot contain an open interval.
Thus the RV-interior in 3.31 has empty ordinary interior. -/
theorem empty_interior_of_finite_last_fibers {X : Type*} [TopologicalSpace X]
    [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    [TopologicalSpace R] [OrderTopology R] {A : Set (X × R)}
    (hfin : ∀ x, {y | (x,y) ∈ A}.Finite) : interior A = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨x,y⟩ hy
  have h : {z | (x,z) ∈ A} ∈ nhds y :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  obtain ⟨l,r,⟨hl,hr⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp h
  exact (Set.Ioo_infinite (hl.trans hr)) ((hfin x).subset hsub)

end GeneralizedEuler.Section3
