module

public import Section4.EulerRetractions
import all Section4.EulerRetractions
import all Section4.GradedValues

/-! The retraction in the partial answer to Question 4.16, in the
groupified coordinates of the balanced presentation in Proposition 4.21. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Polynomial
open scoped TensorProduct

def groupifiedValueInclusion : valueRing →+* Poly ⊗[Poly] valueRing :=
  (Algebra.TensorProduct.includeRight : valueRing →ₐ[Poly] Poly ⊗[Poly] valueRing).toRingHom

theorem groupifiedValue_leftInverse : Function.LeftInverse tensorValueEquiv groupifiedValueInclusion := by
  intro y
  change tensorValueEquiv (1 ⊗ₜ[Poly] y) = y
  change (1 : Poly) • y = y
  exact one_smul _ _

theorem groupifiedValue_injective : Function.Injective groupifiedValueInclusion :=
  groupifiedValue_leftInverse.injective

/-- The exponent is the residue degree. The value factor keeps its own degree. -/
theorem groupifiedValue_homogeneous (i : ℕ) (a : ℤ) (y : valueRing) :
    tensorValueEquiv (residueTensor (C a * X^i) y) =
      ((-1 : valueRing)^i * (a : valueRing)) * (diagonal X)^i * y := by
  rw [tensorValue_pure]
  congr 1
  change diagonal ((C a * X^i).comp (-X)) = _
  simp only [mul_comp,pow_comp,C_comp,X_comp,map_mul,map_pow,map_neg]
  have hz : diagonal (C a) = (a : valueRing) := by
    apply Subtype.ext; exact Prod.ext (by simp [diagonal]) (by simp [diagonal])
  rw [hz,neg_eq_neg_one_mul (diagonal X),mul_pow]
  ring

/-- Transport both maps together along the groupified tensor presentation. -/
theorem groupifiedValue_transport {R : Type*} [CommRing R] (D : Poly ⊗[Poly] valueRing ≃+* R) :
    (tensorValueEquiv.toRingHom.comp D.symm.toRingHom).comp
      (D.toRingHom.comp groupifiedValueInclusion) = RingHom.id valueRing := by
  apply RingHom.ext
  intro y
  exact (congrArg tensorValueEquiv (D.symm_apply_apply _)).trans (groupifiedValue_leftInverse y)

end GeneralizedEuler.Section4
