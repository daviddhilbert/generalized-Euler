module

public import Section3.BoundaryGraphFormula

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

variable {L : Language} {E : Type*} {X V : TCsort → Type*}
    (M : SortedStructure L E X) (v : ∀ s, V s → X s)

def BlockDefinable (s : TCsort) {d : ℕ} (A : Set (Fin d → X s)) : Prop :=
  ∃ φ : SortedFormula L E (AddSortedBlock V s d), ∀ x,
    φ.realize M (appendSortedBlock v x) ↔ x ∈ A

private theorem blockDefinable_empty (s : TCsort) (d : ℕ) :
    BlockDefinable M v s (∅ : Set (Fin d → X s)) := ⟨.falsum,fun _ => Iff.rfl⟩

abbrev branchAt {d : ℕ} (t : SortedTerm L E (AddSortedBlock V .vf d) .vf)
    (x : Fin d → X .vf) := M.rvMap (t.realize M (appendSortedBlock v x))

variable [Zero (X .rv)]

/-- Descending over nonzero fibers gives an actual RV-definable partial
graph over the fixed parameters. Extending the field term by unused RV
variables does not change its realization on any field lift. -/
theorem blockDefinable_constantFiberGraph {d : ℕ} (i : Fin (d+1))
    (t : SortedTerm L E (AddSortedBlock V .vf d) .vf)
    (hz : ∀ u : Fin (d+1) → X .rv, rvZeroTerm.realize M (appendSortedBlock v u) = 0) :
    BlockDefinable M v .rv (constantFiberGraph M.rvMap (branchAt M v t) i) := by
  let W := AddSortedBlock V .rv (d+1)
  let label (j : Fin (d+1)) : W .rv := .inr ⟨j,⟨rfl⟩⟩
  let rename (s) : AddSortedBlock V .vf d s → AddSortedBlock W .vf d s :=
    Sum.elim (fun b => Sum.inl (Sum.inl b)) Sum.inr
  refine ⟨constantFiberGraphFormula label i (t.relabel rename),fun u => ?_⟩
  rw [constantFiberGraphFormula_realize _ _ _ _ _ (hz u)]
  have h (b : Fin d → X .vf) : (t.relabel rename).realize M (appendSortedBlock (appendSortedBlock v u) b) =
      t.realize M (appendSortedBlock v b) := by
    rw [SortedTerm.realize_relabel]
    congr 1
    funext s z
    cases z <;> rfl
  simp only [h]
  rfl

variable [TopologicalSpace (X .rv)] [LinearOrder (X .rv)] [DenselyOrdered (X .rv)]
  [NoMinOrder (X .rv)] [NoMaxOrder (X .rv)] [OrderTopology (X .rv)]

/-- Lemma 3.26 over a named model assignment. The first input is the
coordinatewise conclusion of 3.21 and compactness. The second is 3.16
for a field term, restricted to nonzero RV fibers. The last is the
closure dimension property in the RV sort. The proof constructs all
the chart domains, their induced graphs and the full induction. -/
theorem definable_rv_boundary_dimension
    (zero : ∀ d (u : Fin d → X .rv), rvZeroTerm.realize M (appendSortedBlock v u) = 0)
    (branches : ∀ d A, BlockDefinable M v .vf A → ∀ i : Fin (d+1),
      ∃ T : Finset (SortedTerm L E (AddSortedBlock V .vf d) .vf), ∀ a y,
        y ∈ rvBoundary M.rvMap {z | i.insertNth z a ∈ A} → ∃ t ∈ T, y = branchAt M v t a)
    (partition : ∀ d (t : SortedTerm L E (AddSortedBlock V .vf d) .vf), ∃ (k : ℕ)
      (B : Fin k → Set (Fin d → X .vf)), (∀ j, BlockDefinable M v .vf (B j)) ∧ (∀ a, ∃ j, a ∈ B j) ∧
      ∀ j u, (∀ l, u l ≠ 0) → (∀ a : Fin d → X .vf, M.rvMap ∘ a = u → a ∈ B j) →
        ∀ a b : Fin d → X .vf, M.rvMap ∘ a = u → M.rvMap ∘ b = u → branchAt M v t a = branchAt M v t b)
    (tame : ∀ d (S : Set (Fin d → X .rv)), BlockDefinable M v .rv S → interior S = ∅ → IsNowhereDense S)
    {d : ℕ} (A : Set (Fin d → X .vf)) (hA : BlockDefinable M v .vf A) :
    IsNowhereDense (rvBoundary (fun x => M.rvMap ∘ x) A) ∧
      projectionDimensionWithBot (rvBoundary (fun x => M.rvMap ∘ x) A) < (d : WithBot ℕ) := by
  classical
  apply boundary_dimension_induction M.rvMap (fun _ => BlockDefinable M v .vf) _ d A hA
  intro n S hS
  choose T cover using branches n S hS
  let T₀ := Finset.univ.biUnion T
  let e := Fintype.equivFin (↥T₀)
  let m := Fintype.card (↥T₀)
  let term (j : Fin m) := (e.symm j).val
  choose k B hB cov full using fun j => partition n (term j)
  let k₀ := Finset.univ.sup k
  have le (j : Fin m) : k j ≤ k₀ := Finset.le_sup (Finset.mem_univ j)
  let pad (j : Fin m) (l : Fin k₀) := if h : l.val < k j then B j ⟨l.val,h⟩ else ∅
  refine ⟨m,k₀,fun _ j => branchAt M v (term j),fun _ j => pad j,?_,?_,?_,?_⟩
  · intro _ j l
    change BlockDefinable M v .vf (pad j l)
    by_cases h : l.val < k j
    · simpa [pad,h] using hB j ⟨l.val,h⟩
    · simpa [pad,h] using blockDefinable_empty M v .vf n
  · intro i a y hy
    obtain ⟨t,ht,he⟩ := cover i a y hy
    let j : T₀ := ⟨t,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ht⟩⟩
    exact ⟨e j,by simpa [term,j] using he⟩
  · intro _ j a b ha hn hd
    obtain ⟨l,hl⟩ := split_from_polydisc_partition M.rvMap _ (B j) (cov j) (full j) a b ha hn hd
    exact ⟨⟨l.val,l.isLt.trans_le (le j)⟩,by simpa [pad,l.isLt] using hl⟩
  · intro i j
    exact tame (n+1) _ (blockDefinable_constantFiberGraph M v i (term j) (zero _))

end GeneralizedEuler.Section3
