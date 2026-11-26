module

public import Section4.GeometricResidueLocalizations
import all Section4.LocalizedEuler

/-! The two denominators in the residue ring are the affine line
and the identity-labelled degree-one point. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.SemiringGroupification
open Polynomial
variable {R V T : Type*} [CommSemiring R] [CommSemiring V] [CommSemiring T]
  {r : R →+* T} {v : V →+* T} {χ : R →+* Poly} {G : Ring V ≃+* valueRing}

def residueDenominator (line point : R) : EulerChoice → Ring R
  | .geometric => of R (line+line+point)
  | .bounded => of R point

theorem residue_denominator_coordinates (line point : R) (ht : χ line = -X) (hp : χ point=X) (choice : EulerChoice) :
    lift χ (residueDenominator line point choice) = choice.denominator := by
  cases choice <;> simp [residueDenominator,EulerChoice.denominator,lift_of,map_add,ht,hp]

theorem EulerCoordinates.localized_formulas (c : EulerCoordinates r v χ G)
    (classify : Function.Bijective (lift χ)) (line point : R) (ht : χ line = -X) (hp : χ point=X)
    (u : Ring T) (hu : c.equiv u=special) (choice : EulerChoice) :
    let d := residueDenominator line point choice
    ∃ f : Ring T →+* Localization.Away d,
      Set.range f = Set.range (Int.castRingHom (Localization.Away d)) ∧ f u=0 ∧
      ∀ (x : Ring R) (k : ℕ) (a : ℤ), lift χ x=C a*X^k →
        f (map r x)=algebraMap (Ring R) (Localization.Away d) x * (IsLocalization.Away.invSelf d)^k := by
  let h := residue_denominator_coordinates line point ht hp choice
  exact ⟨c.residueLocalization classify choice _ h,c.residueLocalization_range classify choice _ h,
    c.residueLocalization_special classify choice _ h u hu,
    fun x k a => c.residueLocalization_homogeneous classify choice _ h x a k⟩

end GeneralizedEuler.Section4.SemiringGroupification
