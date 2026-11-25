module

public import Section3.RVBoundaryTheorem
import all Section3.BoundaryGraphFormula
import all Section3.BoundaryBranches
import all Section3.DefinableBoundary

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2 FirstOrder
variable {L : Language} {E : Type*} {X V : TCsort → Type*} {d : ℕ}
    (M : SortedStructure L E X) (v : ∀ s, V s → X s)

theorem BlockDefinable.finiteUnion {J : Type*} [Finite J] {s : TCsort} (B : J → Set (Fin d → X s))
    (hB : ∀ j, BlockDefinable M v s (B j)) : BlockDefinable M v s (⋃ j, B j) := by
  classical
  let := Fintype.ofFinite J
  choose φ hφ using hB
  refine ⟨SortedFormula.anyOf (Finset.univ.toList.map φ),fun a => ?_⟩
  simp [SortedFormula.realize_anyOf,hφ]

theorem BlockDefinable.or {s : TCsort} {A B : Set (Fin d → X s)}
    (hA : BlockDefinable M v s A) (hB : BlockDefinable M v s B) : BlockDefinable M v s (A ∪ B) := by
  obtain ⟨φ,hφ⟩ := hA
  obtain ⟨ψ,hψ⟩ := hB
  exact ⟨φ.disjunction ψ,fun a => (SortedFormula.realize_disjunction M _ _ _).trans ((hφ a).or (hψ a))⟩

/-- The RV-boundary of a definable set is definable over precisely its
old parameters. Two field tuples, with the same displayed RV labels,
witness the two sides of the boundary. -/
theorem blockDefinable_boundary {A : Set (Fin d → X .vf)} (hd : BlockDefinable M v .vf A) :
    BlockDefinable M v .rv (rvBoundary (fun a => M.rvMap ∘ a) A) := by
  obtain ⟨φ,hφ⟩ := hd
  let W := AddSortedBlock V .rv d
  let rename (s) : AddSortedBlock V .vf d s → AddSortedBlock W .vf d s :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let χ := φ.relabel rename
  let label (j : Fin d) : W .rv := .inr ⟨j,⟨rfl⟩⟩
  let fiber : SortedFormula L E (AddSortedBlock W .vf d) := everyCoord (fun j =>
    SortedFormula.equal (rvOf (.var (.inr ⟨j,⟨rfl⟩⟩))) (.var (.inl (label j))))
  refine ⟨((fiber.conjunction χ).exBlock .vf d).conjunction ((fiber.conjunction χ.neg).exBlock .vf d),fun u => ?_⟩
  let w := appendSortedBlock v u
  have slice (a : Fin d → X .vf) : χ.realize M (appendSortedBlock w a) ↔ a ∈ A := by
    rw [show χ = _ from rfl,SortedFormula.realize_relabel]
    have h : (fun s => appendSortedBlock w a s ∘ rename s) = appendSortedBlock v a := by
      funext s j; cases j <;> rfl
    rw [h,hφ]
  have fib (a : Fin d → X .vf) : fiber.realize M (appendSortedBlock w a) ↔ M.rvMap ∘ a = u := by
    simp only [fiber,everyCoord_realize,SortedFormula.realize,rvOf_realize,SortedTerm.realize]
    exact funext_iff.symm
  change (((fiber.conjunction χ).exBlock .vf d).conjunction ((fiber.conjunction χ.neg).exBlock .vf d)).realize M w ↔
    (∃ a ∈ A, M.rvMap ∘ a = u) ∧ ∃ b, M.rvMap ∘ b = u ∧ b ∉ A
  simp only [SortedFormula.realize_conjunction,SortedFormula.realize_exBlock,SortedFormula.realize_neg,fib,slice]
  exact and_congr (exists_congr fun _ => and_comm) Iff.rfl

variable [Zero (X .rv)] [TopologicalSpace (X .rv)] [T1Space (X .rv)]

/-- Lemma 3.28. The finite partition of 3.16–3.17 and the boundary
theorem produce one exceptional set definable over the original base.
The result includes dimension zero and the tuple of length zero. -/
theorem definable_almost_contraction (f : (Fin d → X .vf) → X .vf)
    (zero : ∀ u : Fin d → X .rv, rvZeroTerm.realize M (appendSortedBlock v u) = 0)
    (dense : Dense ({0}ᶜ : Set (X .rv)))
    (parts : ∃ (k : ℕ) (B : Fin k → Set (Fin d → X .vf)), (∀ j, BlockDefinable M v .vf (B j)) ∧
      (∀ a, ∃ j, a ∈ B j) ∧ ∀ j u, (∀ l, u l ≠ 0) →
      (∀ a : Fin d → X .vf, M.rvMap ∘ a = u → a ∈ B j) →
      ∀ a b : Fin d → X .vf, M.rvMap ∘ a = u → M.rvMap ∘ b = u → M.rvMap (f a) = M.rvMap (f b))
    (boundary : ∀ A : Set (Fin d → X .vf), BlockDefinable M v .vf A →
      projectionDimensionWithBot (rvBoundary (fun a => M.rvMap ∘ a) A) < (d : WithBot ℕ))
    (closureDim : ∀ B : Set (Fin d → X .rv), BlockDefinable M v .rv B → interior B = ∅ → IsNowhereDense B) :
    ∃ U : Set (Fin d → X .rv), BlockDefinable M v .rv U ∧ projectionDimensionWithBot U < (d : WithBot ℕ) ∧
      Contractible (fun a : {a : Fin d → X .vf // M.rvMap ∘ a ∉ U} => M.rvMap ∘ a.val)
        M.rvMap (fun a => f a.val) := by
  obtain ⟨k,B,dB,cover,constant⟩ := parts
  let bad j := rvBoundary (fun a => M.rvMap ∘ a) (B j)
  let Z := {u : Fin d → X .rv | ∃ i, u i = 0}
  have dZ : BlockDefinable M v .rv Z := by
    let φ (j : Fin d) : SortedFormula L E (AddSortedBlock V .rv d) := .equal (.var (.inr ⟨j,⟨rfl⟩⟩)) rvZeroTerm
    refine ⟨SortedFormula.anyOf ((List.finRange d).map φ),fun u => ?_⟩
    simp [SortedFormula.realize_anyOf,φ,SortedFormula.realize,SortedTerm.realize,zero,Z]
    rfl
  have db j : BlockDefinable M v .rv (bad j) := blockDefinable_boundary M v (dB j)
  have thin : IsNowhereDense (⋃ j, bad j) := IsNowhereDense.iUnion (fun j =>
    closureDim _ (db j) (dimensionWithBot_lt_arity_iff.mp (boundary _ (dB j))))
  have emp : interior (⋃ j, bad j) = ∅ := eq_empty_of_subset_empty ((interior_mono subset_closure).trans thin.subset)
  refine ⟨Z ∪ ⋃ j, bad j, dZ.or M v (BlockDefinable.finiteUnion M v bad db),
    dimensionWithBot_lt_arity_iff.mpr (empty_interior_with_zero_coordinates dense emp),?_⟩
  intro a b same
  obtain ⟨j,hj⟩ := cover a.val
  have no := a.property
  apply constant j (M.rvMap ∘ a.val) (fun l h => no (Or.inl ⟨l,h⟩)) _ a.val b.val rfl same.symm
  intro z hz
  by_contra outside
  exact no (Or.inr (mem_iUnion_of_mem j ⟨⟨a.val,hj,rfl⟩,z,hz,outside⟩))

end GeneralizedEuler.Section3
