module

public import Section3.ResidueDerivatives
public import Section3.BoundaryInduction
public import Mathlib.Order.Filter.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace GeneralizedEuler.Section3

open Set Filter
open scoped Topology BigOperators

variable {X : Type*} [TopologicalSpace X]

/-- The open locus used at the start of 3.31. The manuscript calls
closure(A) \\ A its frontier. Here Mathlib's frontier is the ordinary
topological boundary, including endpoints belonging to A. -/
theorem open_value_locus {I V : Type*} [Finite I] (A : Set X) (vals : I → X → V)
    (hfin : ∀ i, (vals i '' A).Finite) :
    let boundaries := ⋃ i, ⋃ v ∈ vals i '' A, frontier {x ∈ A | vals i x = v}
    let W := (A \ frontier A) \ boundaries
    IsOpen W ∧ ∀ x ∈ W, ∀ i, ∀ᶠ y in 𝓝 x, vals i y = vals i x := by
  intro boundaries W
  have hclosed : IsClosed boundaries := isClosed_iUnion_of_finite
    (fun i => (hfin i).isClosed_biUnion (fun _ _ => isClosed_frontier))
  refine ⟨?_,?_⟩
  · change IsOpen ((A \ frontier A) \ boundaries)
    rw [self_sdiff_frontier]
    exact isOpen_interior.sdiff hclosed
  · intro x hx i
    let v := vals i x
    have hm : x ∈ {z ∈ A | vals i z = v} := ⟨hx.1.1,rfl⟩
    have hv : v ∈ vals i '' A := ⟨x,hx.1.1,rfl⟩
    have hb : x ∉ frontier {z ∈ A | vals i z = v} :=
      fun h => hx.2 (mem_iUnion.mpr ⟨i,mem_iUnion₂.mpr ⟨v,hv,h⟩⟩)
    have hmem := mem_interior_iff_mem_nhds.mp ((mem_interior_iff_notMem_frontier hm).mpr hb)
    filter_upwards [hmem] with y hy using hy.2

/-- Induct on total order, always staying between zero and the given
multi-index. This iterates the adjacent residue identities of 3.31,
including the intermediate partials required by a differential polynomial. -/
theorem all_partials_of_adjacent {n : ℕ} (p : Fin n → ℕ) (P : (Fin n → ℕ) → Prop)
    (zero : P 0) (step : ∀ q ≤ p, ∀ i, q i ≠ 0 →
      P (Function.update q i (q i - 1)) → P q) :
    ∀ q ≤ p, P q := by
  classical
  intro q
  induction q using (measure (fun v : Fin n → ℕ => ∑ i, v i)).wf.induction with
  | h q ih =>
    intro hqp
    by_cases hz : q = 0
    · simpa [hz] using zero
    have hex : ∃ i, q i ≠ 0 := by
      by_contra! h
      exact hz (funext h)
    obtain ⟨i, hi⟩ := hex
    let q' := Function.update q i (q i - 1)
    have hle (j : Fin n) : q' j ≤ q j := by
      by_cases hj : j = i
      · subst j; simp [q']
      · simp [q',Function.update_of_ne hj]
    apply step q hqp i hi
    apply ih q' _ (fun j => (hle j).trans (hqp j))
    change (∑ j, q' j) < ∑ j, q j
    apply Finset.sum_lt_sum (fun j _ => hle j)
    exact ⟨i,Finset.mem_univ _,by simp [q',Nat.sub_lt (Nat.pos_of_ne_zero hi) Nat.zero_lt_one]⟩

end GeneralizedEuler.Section3
