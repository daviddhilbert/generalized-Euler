module

public import Section4.AffineLifts
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Completion of the direction-space isomorphism in the exponent-field case of 4.11. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F : Type*} [Field F] {m r : ℕ}

/-- Source and target coordinate maps of full column rank extend to one
invertible matrix of the original ambient degree. -/
theorem ambient_coordinate_change (A B : Matrix (Fin m) (Fin r) F)
    (hA : Function.Injective A.mulVecLin) (hB : Function.Injective B.mulVecLin) :
    ∃ U : (Matrix (Fin m) (Fin m) F)ˣ, U.val * A = B := by
  let a := LinearEquiv.ofInjective A.mulVecLin hA
  let b := LinearEquiv.ofInjective B.mulVecLin hB
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq (a.symm.trans b)
  let U : (Matrix (Fin m) (Fin m) F)ˣ :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv g)
  refine ⟨U,Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul]
  apply LinearMap.ext
  intro x
  have hx := hg (a x)
  change (b (a.symm (a x))).val = g (A.mulVecLin x) at hx
  rw [a.symm_apply_apply] at hx
  have hU : Matrix.GeneralLinearGroup.toLin U = LinearMap.GeneralLinearGroup.ofLinearEquiv g :=
    Matrix.GeneralLinearGroup.toLin.apply_symm_apply _
  change U.val.mulVecLin (A.mulVecLin x) = B.mulVecLin x
  rw [← Matrix.GeneralLinearGroup.toLin_apply, hU]
  exact hx.symm

/-- Apply the ambient coordinate change to values in an arbitrary exponent
module. The intercept lies in the specified base value subspace. -/
theorem change_on_affine_cell {V : Type*} [AddCommGroup V] [Module F V]
    (G : Submodule F V) (A B : Matrix (Fin m) (Fin r) F)
    (hA : Function.Injective A.mulVecLin) (hB : Function.Injective B.mulVecLin)
    (a b : Fin m → V) (ha : ∀ i, a i ∈ G) (hb : ∀ i, b i ∈ G) :
    ∃ (U : (Matrix (Fin m) (Fin m) F)ˣ) (δ : Fin m → V),
      (∀ i, δ i ∈ G) ∧ ∀ z : Fin r → V, actRows U.val (actRows A z + a) + δ = actRows B z + b := by
  obtain ⟨U,hU⟩ := ambient_coordinate_change A B hA hB
  refine ⟨U,b - actRows U.val a,fun i => G.sub_mem (hb i) ?_,fun z => ?_⟩
  · exact G.sum_mem fun j _ => G.smul_mem _ (ha j)
  · have split : actRows U.val (actRows A z + a) = actRows U.val (actRows A z) + actRows U.val a := by
      funext i; simp [actRows,smul_add,Finset.sum_add_distrib]
    rw [split,← actRows_mul,hU]; abel

end GeneralizedEuler.Section4
