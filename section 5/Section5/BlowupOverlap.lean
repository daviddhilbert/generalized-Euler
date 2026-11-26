module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Prod

/-! Compare the graded carriers after blowing up two intersecting loci.
A point on the overlap carries one multiplier, including in the lower
degree where that multiplier is zero. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

variable {X M : Type*} (A B : Set X)

private theorem exclusive_union : A ∪ (B \ A) = A ∪ B := by
  classical
  ext x
  change (x ∈ A ∨ x ∈ B ∧ x ∉ A) ↔ x ∈ A ∨ x ∈ B
  by_cases h : x ∈ A <;> simp [h]

/-- Blow up the second locus only on the part left untouched by the
first. In the zero stratum the resulting points are precisely the union. -/
def overlapZero (A B : Set X) : A ⊕ (B \ A : Set X) ≃ (A ∪ B : Set X) := by
  classical
  have disj : Disjoint A (B \ A) := Set.disjoint_left.2 fun _ h h' => h'.2 h
  exact (Equiv.Set.union disj).symm.trans (Set.equivOfEq (exclusive_union A B))

/-- The original degree keeps the common exterior. Each point of the
union carries one nonzero multiplier. -/
def overlapNonzero (A B : Set X) (M : Type*) :
    ((A ∪ B)ᶜ : Set X) ⊕ ((A × M) ⊕ ((B \ A : Set X) × M)) ≃
      ((A ∪ B)ᶜ : Set X) ⊕ ((A ∪ B : Set X) × M) :=
  Equiv.sumCongr (Equiv.refl _) ((Equiv.sumProdDistrib A (B \ A : Set X) M).symm.trans
    (Equiv.prodCongr (overlapZero A B) (Equiv.refl M)))

/-- The two orders agree separately in both grades. -/
theorem graded_overlap_common_refinement (A B : Set X) (M : Type*) :
    Nonempty ((A ⊕ (B \ A : Set X)) ≃ (B ⊕ (A \ B : Set X))) ∧
      Nonempty
        (((A ∪ B)ᶜ : Set X) ⊕ ((A × M) ⊕ ((B \ A : Set X) × M)) ≃
         ((B ∪ A)ᶜ : Set X) ⊕ ((B × M) ⊕ ((A \ B : Set X) × M))) := by
  let q : (A ∪ B : Set X) ≃ (B ∪ A : Set X) := Set.equivOfEq (Set.union_comm _ _)
  let p : ((A ∪ B)ᶜ : Set X) ≃ ((B ∪ A)ᶜ : Set X) :=
    Set.equivOfEq (congrArg (fun C : Set X => Cᶜ) (Set.union_comm _ _))
  exact ⟨⟨(overlapZero A B).trans (q.trans (overlapZero B A).symm)⟩,
    ⟨(overlapNonzero A B M).trans ((Equiv.sumCongr p (Equiv.prodCongr q (Equiv.refl M))).trans
      (overlapNonzero B A M).symm)⟩⟩

end GeneralizedEuler.Section5
