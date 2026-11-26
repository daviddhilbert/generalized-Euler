module

public import Section4.GroupifiedRectangle
public import Section4.LocalizedEuler
public import Section4.GeometricValuePresentation
import all Section4.GroupifiedRectangle
import all Section4.EulerRetractions
import all Section4.GradedValues
import all Section4.EulerRing

/-! Transport of the value coordinates across the actual balanced
rectangle map. Residue polynomials undergo the sign twist at the old
point. The principal quotient and both localized maps are explicit. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Polynomial
namespace SemiringGroupification
variable {R V T : Type*} [CommSemiring R] [CommSemiring V] [CommSemiring T]
  (r : R →+* T) (v : V →+* T) (t : R) (e : V) (balance : r t=v e)
  (χ : R →+* Poly) (line : χ t = -X) (bij : Function.Bijective (rectangleHom r v t e balance))
  (resClass : Function.Bijective (lift χ)) (G : Ring V ≃+* valueRing) (pt : G (of V e)=point)

/-- The field and value factors in the geometric RV ring coordinates. -/
structure EulerCoordinates where
  equiv : Ring T ≃+* valueRing
  on_value : ∀ x, equiv (map v x) = G x
  on_residue : ∀ a, equiv (of T (r a)) = diagonal (signTwist (χ a))

include pt in
def rectangle_euler_coordinates : EulerCoordinates r v χ G := by
  let m := RingEquiv.ofBijective (map v) (groupified_value_map_bijective r v t e balance χ line bij resClass)
  let φ := m.symm.trans G
  have val (x : Ring V) : φ (map v x) = G x := by
    change G (m.symm (m x)) = _
    rw [m.symm_apply_apply]
  have evaluation : G.toRingHom.comp (eval₂RingHom (Int.castRingHom (Ring V)) (-(of V e))) =
      diagonal.comp signTwist.toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change G (eval₂ _ _ X) = diagonal (signTwist X)
      rw [eval₂_X,map_neg,pt]
      change -point = diagonal (X.comp (-X))
      rw [X_comp,map_neg]; rfl
  refine ⟨φ,val,fun a => ?_⟩
  rw [← residueEvaluation_recovers r v t e balance χ line resClass a,val]
  exact DFunLike.congr_fun evaluation (χ a)

namespace EulerCoordinates
variable {r v χ G} (c : EulerCoordinates r v χ G)
  (rayClass : V) (rayCoord : G (of V rayClass)=ray) (pointClass : R) (pointPoly : χ pointClass=X)

/-- The signed punctured ideal contributes the two unsigned ray classes. -/
def specialClass (r : R →+* T) (v : V →+* T) (rayClass : V) (pointClass : R) :=
  1 + of T (v (rayClass+rayClass)) - of T (r pointClass)

include rayCoord pointPoly in
theorem special_image : c.equiv (specialClass r v rayClass pointClass) = special := by
  have vr : c.equiv (of T (v rayClass))=ray := by simpa only [map_of] using (c.on_value (of V rayClass)).trans rayCoord
  have rp : c.equiv (of T (r pointClass)) = -point := by
    rw [c.on_residue,pointPoly]; change diagonal (X.comp (-X)) = -point
    rw [X_comp,map_neg]; rfl
  simp only [specialClass,map_sub,map_add,map_one,vr,rp,special]
  ring

/-- Transfer the two-character quotient through the geometric equivalence. -/
def quotient (u : Ring T) (hu : c.equiv u=special) : (Ring T ⧸ Ideal.span {u}) ≃+* ℤ × ℤ :=
  (Ideal.quotientEquiv _ (Ideal.span {special}) c.equiv (by rw [Ideal.map_span,Set.image_singleton]; change Ideal.span {special} = Ideal.span {c.equiv u}; rw [hu])).trans quotientEulerEquiv

theorem characters (u : Ring T) (hu : c.equiv u=special) (f : (Ring T ⧸ Ideal.span {u}) →+* ℤ) :
    f = (RingHom.fst ℤ ℤ).comp (c.quotient u hu).toRingHom ∨
      f = (RingHom.snd ℤ ℤ).comp (c.quotient u hu).toRingHom := by
  let q := c.quotient u hu
  rcases integer_character (f.comp q.symm.toRingHom) with h|h
  · left; exact RingHom.ext fun x => by simpa [q] using DFunLike.congr_fun h (q x)
  · right; exact RingHom.ext fun x => by simpa [q] using DFunLike.congr_fun h (q x)

def localized (choice : EulerChoice) : Ring T →+* Localization.Away choice.denominator :=
  choice.localized.comp (c.equiv.trans tensorValueEquiv.symm).toRingHom

theorem localized_range (choice : EulerChoice) : Set.range (c.localized choice) =
    Set.range (Int.castRingHom (Localization.Away choice.denominator)) := by
  rw [← choice.degree_zero_range]
  exact (c.equiv.trans tensorValueEquiv.symm).surjective.range_comp _

theorem localized_special (choice : EulerChoice) (u : Ring T) (hu : c.equiv u=special) :
    c.localized choice u=0 := by
  change choice.localized (tensorValueEquiv.symm (c.equiv u))=0
  rw [hu,choice.kills_special]

theorem localized_residue (choice : EulerChoice) (a : R) (z : ℤ) (k : ℕ) (ha : χ a=C z*X^k) :
    c.localized choice (of T (r a)) =
      algebraMap Poly (Localization.Away choice.denominator) (C z*X^k) *
        (IsLocalization.Away.invSelf choice.denominator)^k := by
  change choice.localized (tensorValueEquiv.symm (c.equiv (of T (r a)))) = _
  rw [c.on_residue,ha,← mul_one (diagonal _),← tensorValue_pure,tensorValueEquiv.symm_apply_apply]
  exact choice.on_residue z k

end EulerCoordinates
end SemiringGroupification
end GeneralizedEuler.Section4
