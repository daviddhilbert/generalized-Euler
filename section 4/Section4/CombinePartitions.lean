module

public import Section4.FiniteScissors

/-! Flatten a finite family of disjoint finite partitions and retain both
its carrier and the sum of its weights. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {X A T : Type*} {I : Type} [Fintype I] [AddCommMonoid T]

theorem combine_partitions (carrier : A → Set X) (weight : A → T) (U : I → Set X)
    (disj : Pairwise (fun i j => Disjoint (U i) (U j))) (v : I → T)
    (parts : ∀ i, ∃ (n : ℕ) (a : Fin n → A), Pairwise (fun j k => Disjoint (carrier (a j)) (carrier (a k))) ∧
      (⋃ j, carrier (a j)) = U i ∧ (∑ j, weight (a j)) = v i) :
    ∃ (n : ℕ) (a : Fin n → A), Pairwise (fun j k => Disjoint (carrier (a j)) (carrier (a k))) ∧
      (⋃ j, carrier (a j)) = (⋃ i, U i) ∧ (∑ j, weight (a j)) = ∑ i, v i := by
  classical
  choose n a hd hc hw using parts
  let B := Σ i, Fin (n i)
  let e := (Fintype.equivFin B).symm
  let b (j : B) := a j.1 j.2
  have sub i j : carrier (a i j) ⊆ U i := by rw [← hc]; exact Set.subset_iUnion (fun t => carrier (a i t)) j
  have sep : Pairwise (fun i j : B => Disjoint (carrier (b i)) (carrier (b j))) := by
    rintro ⟨i,s⟩ ⟨j,t⟩ ne
    by_cases eq : i = j
    · subst j; apply hd; exact fun h => ne (congrArg (Sigma.mk i) h)
    · exact (disj eq).mono (sub i s) (sub j t)
  refine ⟨_,b ∘ e,fun i j h => sep (fun eq => h (e.injective eq)),?_,?_⟩
  · change (⋃ j, carrier (b (e j))) = _
    rw [e.surjective.iUnion_comp (fun j => carrier (b j)),Set.iUnion_sigma]
    exact congrArg (fun f : I → Set X => ⋃ i, f i) (funext hc)
  · calc
      (∑ j, weight (b (e j))) = ∑ j : B, weight (b j) := e.sum_comp (fun j => weight (b j))
      _ = ∑ i, ∑ t, weight (a i t) := Fintype.sum_sigma' (fun i t => weight (a i t))
      _ = _ := Finset.sum_congr rfl (fun i _ => hw i)

end GeneralizedEuler.Section4
