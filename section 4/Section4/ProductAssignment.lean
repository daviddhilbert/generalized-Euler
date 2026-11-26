module

public import Section4.AssignedScissors
public import Section4.RVProducts
import all Section4.LocalRVMeasure

/-! Product partitions lift multiplicativity from rectangles to positive
models and then to every tagged presentation. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.LocalRVMeasure
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z}
  {S : SortedSubstructure M} {P : Z .rv → Prop} {k l : ℕ} {T : Type*} [CommSemiring T]
  (μ : LocalRVMeasure M S P k T) (ν : LocalRVMeasure M S P l T) (ρ : LocalRVMeasure M S P (k+l) T)
  {I H : Type} [Finite I] [Finite H] {D : Set (I → Z .rv)} {E : Set (H → Z .rv)}

omit [Finite I] [Finite H] in
theorem product_of_partitions {A B : Type} [Fintype A] [Fintype B]
    (a : A → Set (I → Z .rv)) (b : B → Set (H → Z .rv)) (x : A → T) (y : B → T)
    (da : Pairwise (fun i j => Disjoint (a i) (a j))) (db : Pairwise (fun i j => Disjoint (b i) (b j)))
    (ca : (⋃ i, a i) = D) (cb : (⋃ j, b j) = E)
    (h : ∀ i j, ρ.assigned (productSet (a i) (b j)) (x i * y j)) :
    ρ.assigned (productSet D E) ((∑ i, x i) * ∑ j, y j) := by
  obtain ⟨dj,cv⟩ := product_partitions a b da db ca cb
  have result := ρ.assigned_partition (fun p : A × B => productSet (a p.1) (b p.2))
    (fun p => x p.1 * y p.2) dj cv (fun p => h p.1 p.2)
  rw [Finset.sum_mul]
  simpa only [Fintype.sum_prod_type,Finset.mul_sum] using result

omit [Finite I] [Finite H] in
theorem product_of_models
    (models : ∀ A B (ha : GoodRVSet M S P A) (hb : GoodRVSet M S P B),
      ρ.assigned (productSet A B) (μ.weight A ha * ν.weight B hb))
    {x y : T} (hx : μ.assigned D x) (hy : ν.assigned E y) : ρ.assigned (productSet D E) (x*y) := by
  obtain ⟨_,a,da,ca,rfl⟩ := hx
  obtain ⟨_,b,db,cb,rfl⟩ := hy
  apply ρ.product_of_partitions _ _ _ _ da db ca cb
  intro i j
  exact ρ.transfer (rv_product_equivalent (a i).identifies (b j).identifies)
    (models _ _ (a i).good (b j).good)

end GeneralizedEuler.Section4.LocalRVMeasure
