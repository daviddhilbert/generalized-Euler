module

public import Section4.EulerRetractions
public import Mathlib.RingTheory.Localization.Away.Basic

/-! The two maps of 4.24 have codomains localized at the actual element
of degree one. Their ranges consist exactly of the degree-zero fractions. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Polynomial
open scoped TensorProduct

inductive EulerChoice | geometric | bounded

namespace EulerChoice

def denominator : EulerChoice → Poly
  | geometric => -X
  | bounded => X

def sign : EulerChoice → ℤ
  | geometric => -1
  | bounded => 1

def select : EulerChoice → (ℤ × ℤ →+* ℤ)
  | geometric => RingHom.fst _ _
  | bounded => RingHom.snd _ _

def localized (c : EulerChoice) : Poly ⊗[Poly] valueRing →+* Localization.Away c.denominator :=
  (Int.castRingHom _).comp (c.select.comp residueEvaluations)

theorem constants (c : EulerChoice) (a : ℤ) : c.localized (residueTensor (C a) 1) = a := by
  change ((c.select (residueEvaluations (residueTensor (C a) 1))) : Localization.Away c.denominator) = a
  rw [residueEvaluations_constants]
  cases c <;> rfl

theorem kills_special (c : EulerChoice) : c.localized (tensorValueEquiv.symm special) = 0 := by
  simp [localized,residueEvaluations_kill_special]

theorem degree_zero_range (c : EulerChoice) : Set.range c.localized = Set.range
    (Int.castRingHom (Localization.Away c.denominator)) := by
  ext z
  exact ⟨fun ⟨p,h⟩ => ⟨_,h⟩,fun ⟨a,h⟩ => ⟨_,(c.constants a).trans h⟩⟩

private theorem normalized_X (c : EulerChoice) :
    algebraMap Poly (Localization.Away c.denominator) X *
      IsLocalization.Away.invSelf c.denominator = (c.sign : Localization.Away c.denominator) := by
  cases c with
  | bounded =>
    change algebraMap Poly (Localization.Away (X : Poly)) X * _ = ((1 : ℤ) : Localization.Away (X : Poly))
    rw [Int.cast_one]
    exact IsLocalization.Away.mul_invSelf (S := Localization.Away (X : Poly)) X
  | geometric =>
    change algebraMap Poly (Localization.Away (-X : Poly)) X * IsLocalization.Away.invSelf (S := Localization.Away (-X : Poly)) (-X : Poly) = ((-1 : ℤ) : Localization.Away (-X : Poly))
    rw [Int.cast_neg,Int.cast_one]
    apply neg_eq_iff_eq_neg.mp
    rw [← neg_mul,← map_neg]
    exact IsLocalization.Away.mul_invSelf (S := Localization.Away (-X : Poly)) (-X)

/-- In residue coordinates, x of Euler characteristic a in degree k is a X^k.
The formula also covers k = 0 and the empty class. -/
theorem on_residue (c : EulerChoice) (a : ℤ) (k : ℕ) :
    c.localized (residueTensor (C a * X^k) 1) =
      algebraMap Poly (Localization.Away c.denominator) (C a * X^k) *
        (IsLocalization.Away.invSelf c.denominator)^k := by
  rw [map_mul,map_pow,mul_assoc,← mul_pow,c.normalized_X]
  change ((c.select (residueEvaluations (residueTensor (C a * X^k) 1))) :
    Localization.Away c.denominator) = _
  rw [residueEvaluations_homogeneous]
  have hC : algebraMap Poly (Localization.Away c.denominator) (C a) = a := by
    rw [show (C a : Poly) = (a : Poly) from map_intCast _ _,map_intCast]
  rw [hC]
  cases c <;> simp [select,sign]

end EulerChoice
end GeneralizedEuler.Section4
