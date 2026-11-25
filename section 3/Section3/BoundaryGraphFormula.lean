module

public import Section3.BoundaryCharts
import all Section3.BoundaryCharts
import all Section3.BoundaryBranches
public import Section2.RVMonomials

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

variable {L : Language} {E : Type*} {V Z : TCsort → Type*} {n : ℕ}

/-- A finite conjunction indexed by the coordinates of an RV fiber. -/
private def everyCoord (φ : Fin n → SortedFormula L E V) :=
  SortedFormula.allOf ((List.finRange n).map φ)

private theorem everyCoord_realize (M : SortedStructure L E Z) (φ : Fin n → SortedFormula L E V)
    (v : ∀ s, V s → Z s) : (everyCoord φ).realize M v ↔ ∀ i, (φ i).realize M v := by
  simp [everyCoord,SortedFormula.realize_allOf]

/-- The partial graph in 3.26, written in sorted syntax with free RV
labels, names for ordinary parameters, and quantified VF representatives.
The term t is evaluated on the representatives of the base coordinates. -/
def constantFiberGraphFormula (labels : Fin (n+1) → V .rv) (i : Fin (n+1))
    (t : SortedTerm L E (AddSortedBlock V .vf n) .vf) :
    SortedFormula L E V :=
  let pos := everyCoord (fun j => (SortedFormula.equal (.var (labels (i.succAbove j))) rvZeroTerm).neg)
  let fiber := everyCoord (fun j => SortedFormula.equal
    (rvOf (.var (.inr ⟨j,⟨rfl⟩⟩) : SortedTerm L E (AddSortedBlock V .vf n) .vf))
    (.var (.inl (labels (i.succAbove j)))))
  let value := SortedFormula.equal (rvOf t) (.var (.inl (labels i)))
  pos.conjunction ((fiber.exBlock .vf n).conjunction ((fiber.imp value).allBlock .vf n))

theorem constantFiberGraphFormula_realize [Zero (Z .rv)] (M : SortedStructure L E Z)
    (v : ∀ s, V s → Z s) (labels : Fin (n+1) → V .rv) (i : Fin (n+1))
    (t : SortedTerm L E (AddSortedBlock V .vf n) .vf)
    (hz : (rvZeroTerm : SortedTerm L E V .rv).realize M v = 0) :
    (constantFiberGraphFormula labels i t).realize M v ↔
      v .rv ∘ labels ∈ constantFiberGraph M.rvMap
        (fun b => M.rvMap (t.realize M (appendSortedBlock v b))) i := by
  have fib (b : Fin n → Z .vf) :
      (∀ j, M.rvMap (b j) = v .rv (labels (i.succAbove j))) ↔
        M.rvMap ∘ b = i.removeNth (v .rv ∘ labels) := funext_iff.symm
  simp only [constantFiberGraphFormula,SortedFormula.realize_conjunction,everyCoord_realize,
    SortedFormula.realize_exBlock,SortedFormula.realize_allBlock,SortedFormula.realize_neg,
    SortedFormula.realize,rvOf_realize,SortedTerm.realize,appendSortedBlock,hz]
  change ((∀ j, v .rv (labels (i.succAbove j)) ≠ 0) ∧
      (∃ b : Fin n → Z .vf, ∀ j, M.rvMap (b j) = v .rv (labels (i.succAbove j))) ∧
      ∀ b : Fin n → Z .vf, (∀ j, M.rvMap (b j) = v .rv (labels (i.succAbove j))) →
        M.rvMap (t.realize M (appendSortedBlock v b)) = v .rv (labels i)) ↔ _
  simp only [fib]
  rfl

/-- A finite partition from 3.16 supplies the splitting predicates
needed in the boundary induction. Finding a part containing the first
representative suffices, since a full nonzero fiber in that part has a
single output label. -/
theorem split_from_polydisc_partition {K R : Type*} [Zero R] {I : Type*}
    (p : K → R) (f : (Fin n → K) → R) (D : I → Set (Fin n → K))
    (cover : ∀ a, ∃ j, a ∈ D j)
    (constant : ∀ j u, (∀ k, u k ≠ 0) → (∀ a : Fin n → K, p ∘ a = u → a ∈ D j) →
      ∀ a b : Fin n → K, p ∘ a = u → p ∘ b = u → f a = f b)
    (a b : Fin n → K) (same : p ∘ a = p ∘ b) (nz : ∀ j, p (a j) ≠ 0) (dif : f a ≠ f b) :
    ∃ j, p ∘ a ∈ rvBoundary (fun x => p ∘ x) (D j) := by
  obtain ⟨j,hj⟩ := cover a
  refine ⟨j,⟨a,hj,rfl⟩,?_⟩
  by_contra! no
  exact dif (constant j (p ∘ a) nz no a b rfl same.symm)

end GeneralizedEuler.Section3
