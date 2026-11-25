module

public import Section3.BoundaryBranches
public import Section3.DefinablePartitions

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K R : Type*} [Zero R] {n : ℕ}

/-- The graph of the induced branch on nonzero labels for which the branch
has a single value on the entire fiber. This description by field witnesses
does not require a section of the leading term map. -/
def constantFiberGraph (p : K → R) (f : (Fin n → K) → R) (i : Fin (n+1)) :
    Set (Fin (n+1) → R) :=
  {u | (∀ j, i.removeNth u j ≠ 0) ∧
    (∃ a, p ∘ a = i.removeNth u) ∧ ∀ b, p ∘ b = i.removeNth u → f b = u i}

private theorem constantFiberGraph_functional (p : K → R) (f : (Fin n → K) → R)
    (i : Fin (n+1)) {u v : Fin (n+1) → R} (hu : u ∈ constantFiberGraph p f i)
    (hv : v ∈ constantFiberGraph p f i) (he : i.removeNth u = i.removeNth v) : u i = v i := by
  obtain ⟨a,ha⟩ := hu.2.1
  exact (hu.2.2 a ha).symm.trans (hv.2.2 a (ha.trans he))

variable [TopologicalSpace R] [LinearOrder R] [DenselyOrdered R] [NoMinOrder R]
  [NoMaxOrder R] [OrderTopology R]

theorem constantFiberGraph_empty_interior (p : K → R) (f : (Fin n → K) → R)
    (i : Fin (n+1)) : interior (constantFiberGraph p f i) = ∅ := by
  classical
  let g (a : Fin n → R) := if h : ∃ u ∈ constantFiberGraph p f i, i.removeNth u = a
    then h.choose i else 0
  have sub : constantFiberGraph p f i ⊆ {u | ∃ _ : Unit, u i = g (i.removeNth u)} := by
    intro u hu
    have existsLift : ∃ v ∈ constantFiberGraph p f i, i.removeNth v = i.removeNth u := ⟨u,hu,rfl⟩
    refine ⟨(),?_⟩
    dsimp [g]
    rw [dite_eq_left existsLift]
    exact constantFiberGraph_functional p f i hu existsLift.choose_spec.1 existsLift.choose_spec.2.symm
  exact eq_empty_of_subset_empty ((interior_mono sub).trans (empty_interior_coordinate_graphs i (fun _ : Unit => g)).subset)

omit [TopologicalSpace R] [DenselyOrdered R] [NoMinOrder R] [NoMaxOrder R] [OrderTopology R] in
/-- Any full nonzero base fiber that meets no boundary of a splitting test
lies in one cell of its finite truth partition. Corollary 3.16 then makes
the branch single-valued on the base fiber. -/
theorem boundary_cover_by_splitting_tests {J I : Type*} (p : K → R)
    (A : Set (Fin (n+1) → K))
    (f : Fin (n+1) → J → (Fin n → K) → R)
    (B : Fin (n+1) → J → I → Set (Fin n → K))
    (labels : ∀ i a t, t ∈ rvBoundary p {v | i.insertNth v a ∈ A} →
      ∃ j, t = f i j a)
    (split : ∀ i j (a b : Fin n → K), p ∘ a = p ∘ b → (∀ k, p (a k) ≠ 0) →
      f i j a ≠ f i j b → ∃ l, p ∘ a ∈ rvBoundary (fun x => p ∘ x) (B i j l))
    {u : Fin (n+1) → R} (hu : u ∈ rvBoundary (fun x => p ∘ x) A) :
    (∃ i, u i = 0) ∨ ∃ i j, u ∈ constantFiberGraph p (f i j) i ∨
      ∃ l, i.removeNth u ∈ rvBoundary (fun x => p ∘ x) (B i j l) := by
  classical
  by_cases zero : ∃ i, u i = 0
  · exact Or.inl zero
  right
  obtain ⟨i,z,w,hz,hw,hzt,hwt,agree⟩ := boundary_witness_in_coordinate_slice p A hu
  let a := i.removeNth z
  have ha : p ∘ a = i.removeNth u := funext fun j => congrFun hzt (i.succAbove j)
  have hwa : a = i.removeNth w := funext fun j => agree _ (i.succAbove_ne j)
  have hc : u i ∈ rvBoundary p {v | i.insertNth v a ∈ A} := by
    refine ⟨⟨z i,?_,congrFun hzt i⟩,w i,congrFun hwt i,?_⟩
    · simpa only [a,mem_ofPred_eq,Fin.insertNth_self_removeNth] using hz
    · simpa only [mem_ofPred_eq,hwa,Fin.insertNth_self_removeNth] using hw
  obtain ⟨j,hj⟩ := labels i a _ hc
  refine ⟨i,j,?_⟩
  by_cases cut : ∃ l, i.removeNth u ∈ rvBoundary (fun x => p ∘ x) (B i j l)
  · exact Or.inr cut
  have nz (k : Fin n) : i.removeNth u k ≠ 0 := fun h => zero ⟨i.succAbove k,h⟩
  refine Or.inl ⟨nz,⟨a,ha⟩,fun b hb => ?_⟩
  rw [hj]
  by_contra ne
  obtain ⟨l,hl⟩ := split i j a b (ha.trans hb.symm) (fun k h => nz k ((congrFun ha k).symm.trans h)) (Ne.symm ne)
  exact cut ⟨l,ha ▸ hl⟩

/-- The induction of 3.26 in every arity. The arity-n inputs are the
finite term list of 3.21 and compactness, its finite splitting schemes
from 3.16, and closure tameness of the definable RV graphs (2.27).
Zero-coordinate labels are included in closed coordinate hyperplanes. -/
theorem boundary_dimension_induction (p : K → R)
    (D : (d : ℕ) → Set (Set (Fin d → K)))
    (charts : ∀ d, ∀ A ∈ D (d+1), ∃ (m k : ℕ)
      (f : Fin (d+1) → Fin m → (Fin d → K) → R)
      (B : Fin (d+1) → Fin m → Fin k → Set (Fin d → K)),
      (∀ i j l, B i j l ∈ D d) ∧
      (∀ i a t, t ∈ rvBoundary p {v | i.insertNth v a ∈ A} → ∃ j, t = f i j a) ∧
      (∀ i j (a b : Fin d → K), p ∘ a = p ∘ b → (∀ l, p (a l) ≠ 0) →
        f i j a ≠ f i j b → ∃ l, p ∘ a ∈ rvBoundary (fun x => p ∘ x) (B i j l)) ∧
      ∀ i j, interior (constantFiberGraph p (f i j) i) = ∅ →
        IsNowhereDense (constantFiberGraph p (f i j) i)) :
    ∀ d, ∀ A ∈ D d, IsNowhereDense (rvBoundary (fun x => p ∘ x) A) ∧
      projectionDimensionWithBot (rvBoundary (fun x => p ∘ x) A) < (d : WithBot ℕ) := by
  intro d
  induction d with
  | zero =>
    intro A _
    have he : rvBoundary (fun x => p ∘ x) A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨i,_⟩ := boundary_witness_in_coordinate_slice p A hu
      exact i.elim0
    simp [he,projectionDimensionWithBot,IsNowhereDense]
  | succ d ih =>
    intro A hA
    obtain ⟨m,k,f,B,hB,labels,split,tame⟩ := charts d A hA
    let Z := {u : Fin (d+1) → R | ∃ i, u i = 0}
    have closedZ : IsClosed Z := by
      have hz : Z = ⋃ i : Fin (d+1), (fun u : Fin (d+1) → R => u i) ⁻¹' {0} := by ext; simp [Z]
      rw [hz]
      exact isClosed_iUnion_of_finite fun i => isClosed_singleton.preimage (continuous_apply i)
    have thinZ : IsNowhereDense Z := by
      rw [IsNowhereDense,closedZ.closure_eq]
      simpa [Z] using empty_interior_with_zero_coordinates (n := d+1)
        (dense_compl_singleton (0 : R)) (A := ∅) interior_empty
    let G (i : Fin (d+1)) (j : Fin m) := constantFiberGraph p (f i j) i
    let C (i : Fin (d+1)) (j : Fin m) (l : Fin k) :=
      (fun u : Fin (d+1) → R => i.removeNth u) ⁻¹' rvBoundary (fun x => p ∘ x) (B i j l)
    have thin : IsNowhereDense (Z ∪ ⋃ i, ⋃ j, G i j ∪ ⋃ l, C i j l) := by
      apply thinZ.union
      apply IsNowhereDense.iUnion
      intro i
      apply IsNowhereDense.iUnion
      intro j
      exact (tame i j (constantFiberGraph_empty_interior p _ i)).union (IsNowhereDense.iUnion
        (fun l => nowhereDense_coordinate_cylinder i (ih _ (hB i j l)).1))
    have hb : IsNowhereDense (rvBoundary (fun x => p ∘ x) A) := thin.mono (by
      intro u hu
      rcases boundary_cover_by_splitting_tests p A f B labels split hu with hz | ⟨i,j,h⟩
      · exact Or.inl hz
      · refine Or.inr (mem_iUnion_of_mem i (mem_iUnion_of_mem j ?_))
        exact h.imp_right (fun ⟨l,hl⟩ => mem_iUnion_of_mem l hl))
    exact ⟨hb,dimensionWithBot_lt_arity_iff.mpr (eq_empty_of_subset_empty
      ((interior_mono subset_closure).trans hb.subset))⟩

end GeneralizedEuler.Section3
