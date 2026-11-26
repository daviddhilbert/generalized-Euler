module

public import Section4.Scissors
public import Section4.GraphCharts
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Positive tensor comparison. In both arguments equality is established
by adding the matched and residual terms, so no cancellation is required. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
open scoped TensorProduct
open GeneralizedEuler.Section2 FirstOrder

section PositiveTensor
variable {C R V : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring V]
  [Algebra C R] [Algebra C V]

theorem balance_rank_drop (e : C) (b : R) (d : V) (lost : ℕ) :
    b ⊗ₜ[C] (algebraMap C V e ^ lost * d) =
      (b * algebraMap C R e ^ lost) ⊗ₜ[C] d := by
  simp only [← map_pow, ← Algebra.smul_def, mul_comm b]
  exact TensorProduct.tmul_smul _ _ _

structure Rectangle (R V : Type*) where
  residue : R
  value : V

def rectangleSum (l : List (Rectangle R V)) : R ⊗[C] V :=
  (l.map fun p => p.residue ⊗ₜ[C] p.value).sum

theorem rectangleSum_append (x y : List (Rectangle R V)) :
    rectangleSum (C := C) (x++y) = rectangleSum x + rectangleSum y := by
  simp [rectangleSum]

/-- A graph chart may project using different free coordinates on the two
sides. Equality of the two *classes* suffices for the tensor sum. -/
theorem graph_piece_sum {n : ℕ} (source target : Fin n → Rectangle R V)
    (res : ∀ i, (source i).residue = (target i).residue)
    (val : ∀ i, (source i).value = (target i).value) :
    rectangleSum (C := C) (List.ofFn source) = rectangleSum (List.ofFn target) := by
  have he : source = target := funext fun i => by
    cases h : source i; cases h' : target i
    have hr := res i; have hv := val i
    simp [h,h'] at hr hv
    simp [hr,hv]
  rw [he]

/-- The second proof of 4.21, by height of the unmatched rectangles.
At height zero there can be no nonempty residual comparison. -/
theorem equal_by_height {P : Type*} (height : P → ℕ)
    (source target : P → List (Rectangle R V))
    (cut : ∀ p, ∃ (matched : List (Rectangle R V)) (rest : List P),
      (∀ q ∈ rest, height q < height p) ∧
      rectangleSum (C := C) (source p) =
        rectangleSum matched + (rest.map fun q => rectangleSum (source q)).sum ∧
      rectangleSum (C := C) (target p) =
        rectangleSum matched + (rest.map fun q => rectangleSum (target q)).sum) :
    ∀ p, rectangleSum (C := C) (source p) = rectangleSum (target p) := by
  intro p
  induction hk : height p using Nat.strong_induction_on generalizing p with
  | h k ih =>
    obtain ⟨m,r,hr,hs,ht⟩ := cut p
    rw [hs,ht]
    congr 2
    apply List.map_congr_left
    intro q hq
    exact ih (height q) (hk ▸ hr q hq) q rfl

end PositiveTensor

section Isomorphism
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
  (M : SortedStructure L E Z) (S : SortedSubstructure M)
  {C R V : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring V]
  [Algebra C R] [Algebra C V]

/-- The chart assignment is checked on object relations; on products of
generators it returns the pure tensor. Both inverse identities then follow
on arbitrary elements of the two semirings. -/
def tensorIsoOfCharts (D : R ⊗[C] V →+* RVSemiring M S)
    (charts : GradedObject M S → List (Rectangle R V))
    (respects : ∀ a b, RVRelation M S a b →
      MvPolynomial.eval₂ (Nat.castRingHom _) (fun U => rectangleSum (C := C) (charts U)) a =
      MvPolynomial.eval₂ (Nat.castRingHom _) (fun U => rectangleSum (C := C) (charts U)) b)
    (covers : ∀ U, D (rectangleSum (C := C) (charts U)) = objectClass M S U)
    (products : ∀ x y, ∃ u : RVExpression M S,
      D (x ⊗ₜ[C] y) = (ringConGen (RVRelation M S)).mk' u ∧
      MvPolynomial.eval₂ (Nat.castRingHom _) (fun U => rectangleSum (C := C) (charts U)) u =
        x ⊗ₜ[C] y) : R ⊗[C] V ≃+* RVSemiring M S := by
  let w := fun U => rectangleSum (C := C) (charts U)
  let back := descendWeights M S w respects
  have left (a) : back (D a) = a := by
    induction a using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨u,hu,he⟩ := products x y
      rw [hu]
      exact he
    | add x y hx hy => simp only [map_add,hx,hy]
  have right (b) : D (back b) = b := by
    obtain ⟨p,rfl⟩ := (ringConGen (RVRelation M S)).mk'_surjective b
    induction p using MvPolynomial.induction_on with
    | C n => simp [show MvPolynomial.C n = (n : RVExpression M S) from map_natCast _ n]
    | add x y hx hy => simp only [map_add,hx,hy]
    | mul_X p i hp =>
      simp only [map_mul,hp]
      apply congrArg (_ * ·)
      change D (descendWeights M S w respects (objectClass M S i)) = objectClass M S i
      rw [descendWeights_class]
      exact covers i
  exact RingEquiv.ofBijective D ⟨Function.LeftInverse.injective left,
    Function.RightInverse.surjective right⟩

end Isomorphism

section Heights
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  (v : T →ₗ[F] V) (G : Submodule F V)

/-- With equal spans an independent input of maximal height forces the
output height and independence, including for the empty tuple. -/
theorem independent_at_max_height {m n : ℕ} (x : Fin m → T) (y : Fin n → T)
    (h : LinearIndependent F (G.mkQ ∘ v ∘ x)) (hs : valueSpan v G x = valueSpan v G y)
    (hn : n ≤ m) : n = m ∧ LinearIndependent F (G.mkQ ∘ v ∘ y) := by
  have hx := finrank_span_eq_card h
  change Module.finrank F (valueSpan v G x) = _ at hx
  rw [hs, Fintype.card_fin] at hx
  have hy := finrank_range_le_card (R := F) (G.mkQ ∘ v ∘ y)
  change Module.finrank F (valueSpan v G y) ≤ _ at hy
  rw [Fintype.card_fin,hx] at hy
  obtain rfl := hn.antisymm hy
  refine ⟨rfl,linearIndependent_iff_card_eq_finrank_span.mpr ?_⟩
  rw [Fintype.card_fin]
  exact hx.symm

end Heights
end GeneralizedEuler.Section4
