module

public import Section4.GradedValues
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! The finite-value point acts by -X in residue Euler coordinates and by X
in the value ring. Transport along the sign involution implements this action. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
open Polynomial
open scoped TensorProduct

def signTwist : Poly ≃+* Poly where
  __ := Polynomial.compRingHom (-X)
  invFun p := p.comp (-X)
  left_inv := comp_neg_X_comp_neg_X
  right_inv := comp_neg_X_comp_neg_X

instance : Algebra Poly valueRing := diagonal.toAlgebra

/-- Tensor coordinates expressed in the finite-value polynomial parameter. -/
def residueTensor (p : Poly) (y : valueRing) : Poly ⊗[Poly] valueRing :=
  signTwist p ⊗ₜ[Poly] y

def tensorValueEquiv : Poly ⊗[Poly] valueRing ≃+* valueRing :=
  (Algebra.TensorProduct.lid Poly valueRing).toRingEquiv

theorem tensorValue_pure (p : Poly) (y : valueRing) :
    tensorValueEquiv (residueTensor p y) = diagonal (signTwist p) * y := by
  change (signTwist p) • y = _
  rw [Algebra.smul_def]; rfl

/-- Balancing holds for every polynomial in the finite-value generator. -/
theorem residueTensor_balanced (f x : Poly) (y : valueRing) :
    residueTensor (signTwist f * x) y = residueTensor x (diagonal f * y) := by
  apply tensorValueEquiv.injective
  rw [tensorValue_pure,tensorValue_pure,map_mul]
  have hf : signTwist (signTwist f) = f := comp_neg_X_comp_neg_X f
  rw [hf,map_mul]
  ring

/-- The two integer evaluations after inverting the degree-one class.
The integer is the degree-zero coordinate in the corresponding localization. -/
def residueEvaluations : Poly ⊗[Poly] valueRing →+* ℤ × ℤ :=
  evaluations.comp tensorValueEquiv.toRingHom

theorem residueEvaluations_pure (x : Poly) (y : valueRing) :
    residueEvaluations (residueTensor x y) =
      (x.eval (-1) * y.val.1.eval 1, x.eval 1 * y.val.2.eval (-1)) := by
  change evaluations (tensorValueEquiv _) = _
  rw [tensorValue_pure,map_mul]
  change (((x.comp (-X)).eval 1, (x.comp (-X)).eval (-1)) * _) = _
  simp [eval_comp, evaluations]

theorem residueEvaluations_homogeneous (a : ℤ) (k : ℕ) :
    residueEvaluations (residueTensor (C a * X^k) 1) = (a * (-1)^k, a) := by
  rw [residueEvaluations_pure]
  simp

theorem residueEvaluations_kill_special : residueEvaluations (tensorValueEquiv.symm special) = 0 := by
  change evaluations (tensorValueEquiv (tensorValueEquiv.symm special)) = _
  rw [RingEquiv.apply_symm_apply]
  exact (show special ∈ RingHom.ker evaluations by
    rw [ker_evaluations]; exact Ideal.subset_span (by simp))

/-- Each integer actually occurs in both degree-zero ranges. -/
theorem residueEvaluations_constants (a : ℤ) :
    residueEvaluations (residueTensor (C a) 1) = (a,a) := by
  rw [residueEvaluations_pure]; simp

theorem quotient_character (f : (valueRing ⧸ Ideal.span {special}) →+* ℤ) :
    f = (RingHom.fst ℤ ℤ).comp quotientEulerEquiv.toRingHom ∨
      f = (RingHom.snd ℤ ℤ).comp quotientEulerEquiv.toRingHom := by
  rcases integer_character (f.comp quotientEulerEquiv.symm.toRingHom) with h | h
  · left
    apply RingHom.ext
    intro p
    simpa using DFunLike.congr_fun h (quotientEulerEquiv p)
  · right
    apply RingHom.ext
    intro p
    simpa using DFunLike.congr_fun h (quotientEulerEquiv p)

end GeneralizedEuler.Section4
