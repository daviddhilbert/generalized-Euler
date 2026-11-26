module

public import Section4.TensorComparison

/-! A rank-lowering subdivision transfers the lost value coordinates
to unrestricted positive residue factors. Products of the two subdivisions
are summed before any use of groupification. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open scoped TensorProduct
variable {C R V : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring V]
  [Algebra C R] [Algebra C V]

/-- Scissors on an old value cell and on the new residue factors, with all
ambient powers retained. The local equations are ordinary scissor sums in
the two factors, so they may be checked independently of the tensor map. -/
theorem refine_rectangle {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
    (e : C) (b : R) (d : V) (lost : I → ℕ) (value : I → V) (residue : (i : I) → J i → R)
    (valueCut : d = ∑ i, algebraMap C V e ^ lost i * value i)
    (residueCut : ∀ i, b * algebraMap C R e ^ lost i = ∑ j, residue i j) :
    b ⊗ₜ[C] d = ∑ i, ∑ j, residue i j ⊗ₜ[C] value i := by
  rw [valueCut,TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [balance_rank_drop,residueCut,TensorProduct.sum_tmul]

/-- Sum over the projections of graph pieces, using an arbitrary indexing
of the pieces on the two sides. A single graph piece contributes one term
in the source degree. -/
theorem compare_chart_partitions {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] (source : I → R ⊗[C] V) (target : J → R ⊗[C] V)
    (src : K → I) (dst : K → J) (bs bt : K → R) (ds dt : K → V)
    (hs : ∀ i, source i = ∑ k : {k // src k = i}, bs k ⊗ₜ[C] ds k)
    (ht : ∀ j, target j = ∑ k : {k // dst k = j}, bt k ⊗ₜ[C] dt k)
    (residue : ∀ k, bs k = bt k) (value : ∀ k, ds k = dt k) :
    ∑ i, source i = ∑ j, target j := by
  simp_rw [hs,ht]
  rw [Fintype.sum_fiberwise src (fun k => bs k ⊗ₜ[C] ds k),
    Fintype.sum_fiberwise dst (fun k => bt k ⊗ₜ[C] dt k)]
  exact Finset.sum_congr rfl fun k _ => by rw [residue,value]

/-- The old pointwise product requirement fails on any rectangle with two
distinct residue parameters and a nonempty lifted value set. -/
theorem shear_not_constant_on_rectangle {K : Type*} [Group K] (U D : Set K) (hD : D.Nonempty)
    (q : K → K) (factor : ∀ u ∈ U, ∀ t ∈ D, u*t = q t) : U.Subsingleton := by
  obtain ⟨t,ht⟩ := hD
  intro x hx y hy
  exact mul_right_cancel ((factor x hx t ht).trans (factor y hy t ht).symm)

end GeneralizedEuler.Section4
