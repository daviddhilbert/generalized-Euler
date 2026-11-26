module

public import Section4.FrameComparison
public import Section4.MatchingRectangles
import all Section4.ValueStratification

/-! Independent tuples, maximal height, and the strict drop on each
unmatched value stratum in the second proof of Proposition 4.21. -/
public section
namespace GeneralizedEuler.Section4
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {G : Submodule F V} {n r : ℕ}

theorem no_independent_rank_drop (a : ValueFrame G r n) (D : Set (Fin r → V))
    (hi : ∃ x ∈ D, LinearIndependent F (G.mkQ ∘ x))
    (missing : ∀ y ∈ a.eval '' D, ¬ LinearIndependent F (G.mkQ ∘ y)) : r < n := by
  have le : r ≤ n := by simpa using Fintype.card_le_of_injective _ a.free.injective
  apply lt_of_le_of_ne le
  rintro rfl
  obtain ⟨x,hx,ind⟩ := hi
  let e := Equiv.ofBijective a.free ⟨a.free.injective,Finite.surjective_of_injective a.free.injective⟩
  have h : LinearIndependent F ((G.mkQ ∘ a.eval x) ∘ e) := by
    change LinearIndependent F (G.mkQ ∘ (a.eval x ∘ a.free)); rw [a.project_eval]; exact ind
  exact missing _ ⟨x,hx,rfl⟩ ((linearIndependent_equiv e).mp h)

theorem unmatched_stratification {P : ∀ n, Set (Fin n → V) → Prop}
    (cut : ∀ {k l} (p : Fin l → ValuePivot G k) (D) (i), P _ D → P _ (firstPivot p D i))
    (sat : RealizesAffineAvoidance G P) {D : Set (Fin n → V)} (hd : P n D)
    (noIndependent : ∀ x ∈ D, ¬LinearIndependent F (G.mkQ ∘ x)) :
    ∃ (l : ℕ) (a : Fin l → IndependentPiece P G n),
      (∀ i, (a i).rank < n) ∧ D = ⋃ i, (a i).support ∧
      Pairwise (fun i j => Disjoint (a i).support (a j).support) := by
  obtain ⟨l,a,h⟩ := stratify_values P cut sat D hd
  refine ⟨l,a,fun i => no_independent_rank_drop (a i).frame (a i).domain (a i).independent
    (fun x hx => noIndependent x ((h x).1.mpr ⟨i,hx⟩)),?_,?_⟩
  · ext x; exact (h x).1.trans Set.mem_iUnion.symm
  · intro i j he; exact Set.disjoint_left.mpr fun x hi hj => he ((h x).2 i j hi hj)

end GeneralizedEuler.Section4
