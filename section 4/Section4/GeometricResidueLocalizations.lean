module

public import Section4.RectangleEulerCoordinates
import all Section4.RectangleEulerCoordinates
import all Section4.EulerRetractions
import all Section4.SemiringGroupification

/-! The codomains in Proposition 4.24 are localizations of the actual
residue Grothendieck ring. The formulas hold on every homogeneous group
element, including formal differences. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.SemiringGroupification.EulerCoordinates
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R V T : Type*} [CommSemiring R] [CommSemiring V] [CommSemiring T]
  {r : R →+* T} {v : V →+* T} {χ : R →+* Poly} {G : Ring V ≃+* valueRing}
  (c : EulerCoordinates r v χ G) (resClass : Function.Bijective (lift χ))

theorem on_groupified_residue (x : Ring R) : c.equiv (map r x) = diagonal (signTwist (lift χ x)) := by
  have eq : c.equiv.toRingHom.comp (map r) =
      diagonal.comp (signTwist.toRingHom.comp (lift χ)) := by
    apply hom_ext
    intro a
    change c.equiv (map r (of R a)) = diagonal (signTwist (lift χ (of R a)))
    rw [map_of,lift_of,c.on_residue]
  exact DFunLike.congr_fun eq x

variable (choice : EulerChoice) (d : Ring R) (hd : lift χ d=choice.denominator)

def awayCoordinates : Localization.Away d ≃+* Localization.Away choice.denominator :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers d) (T := Submonoid.powers choice.denominator)
    (Localization.Away d) (Localization.Away choice.denominator) (RingEquiv.ofBijective (lift χ) resClass) (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hd)

theorem away_algebraMap (x : Ring R) :
    awayCoordinates resClass choice d hd (algebraMap (Ring R) (Localization.Away d) x) =
      algebraMap Poly (Localization.Away choice.denominator) (lift χ x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

theorem away_inverse :
    awayCoordinates resClass choice d hd (IsLocalization.Away.invSelf d) =
      IsLocalization.Away.invSelf choice.denominator := by
  let q := awayCoordinates resClass choice d hd
  let y := algebraMap Poly (Localization.Away choice.denominator) choice.denominator
  have left : y * q (IsLocalization.Away.invSelf d)=1 := by
    rw [show y = q (algebraMap _ _ d) from (away_algebraMap resClass choice d hd d).trans (congrArg _ hd) |>.symm,
      ← map_mul,IsLocalization.Away.mul_invSelf (S := Localization.Away d) d,map_one]
  have right : y * IsLocalization.Away.invSelf choice.denominator=1 := IsLocalization.Away.mul_invSelf (S := Localization.Away choice.denominator) _
  calc q (IsLocalization.Away.invSelf d) = (y * IsLocalization.Away.invSelf choice.denominator) * q (IsLocalization.Away.invSelf d) := by rw [right,one_mul]
       _ = (y * q (IsLocalization.Away.invSelf d)) * IsLocalization.Away.invSelf choice.denominator := by ring
       _ = _ := by rw [left,one_mul]

def residueLocalization : Ring T →+* Localization.Away d :=
  (awayCoordinates resClass choice d hd).symm.toRingHom.comp (c.localized choice)

theorem residueLocalization_range : Set.range (c.residueLocalization resClass choice d hd) =
    Set.range (Int.castRingHom (Localization.Away d)) := by
  let q := awayCoordinates resClass choice d hd
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨z,h⟩ := (c.localized_range choice) ▸ (show c.localized choice x ∈ Set.range (c.localized choice) from ⟨_,rfl⟩)
    exact ⟨z,by change _ = q.symm (c.localized choice x); rw [← h]; simp⟩
  · rintro ⟨z,rfl⟩
    have mem : (Int.castRingHom (Localization.Away choice.denominator)) z ∈ Set.range (Int.castRingHom _) := ⟨z,rfl⟩
    rw [← c.localized_range choice] at mem
    obtain ⟨x,h⟩ := mem
    exact ⟨x,by change q.symm (c.localized choice x) = _; rw [h]; simp⟩

theorem residueLocalization_special (u : Ring T) (hu : c.equiv u=special) :
    c.residueLocalization resClass choice d hd u=0 := by
  change (awayCoordinates resClass choice d hd).symm (c.localized choice u)=0
  rw [c.localized_special choice u hu,map_zero]

theorem residueLocalization_homogeneous (x : Ring R) (z : ℤ) (k : ℕ) (hx : lift χ x=C z*X^k) :
    c.residueLocalization resClass choice d hd (map r x) =
      algebraMap (Ring R) (Localization.Away d) x * (IsLocalization.Away.invSelf d)^k := by
  let q := awayCoordinates resClass choice d hd
  apply q.injective
  change q (q.symm (choice.localized (tensorValueEquiv.symm (c.equiv (map r x)))))=_
  rw [q.apply_symm_apply,c.on_groupified_residue,hx,← mul_one (diagonal _),← tensorValue_pure,
      tensorValueEquiv.symm_apply_apply,choice.on_residue]
  rw [map_mul q,map_pow q]
  change _ = awayCoordinates resClass choice d hd _ * (awayCoordinates resClass choice d hd _)^k
  rw [away_algebraMap,away_inverse,hx]

/-- A degree-zero fraction has a homogeneous numerator in the same degree
as its denominator. These fractions constitute the entire range. -/
theorem residueLocalization_degree_zero (y : Localization.Away d) :
    y ∈ Set.range (c.residueLocalization resClass choice d hd) ↔
      ∃ (x : Ring R) (k : ℕ) (a : ℤ), lift χ x = C a * X^k ∧
        algebraMap (Ring R) (Localization.Away d) x * (IsLocalization.Away.invSelf d)^k = y := by
  constructor
  · intro hy
    rw [c.residueLocalization_range resClass choice d hd] at hy
    obtain ⟨a,rfl⟩ := hy
    exact ⟨a,0,a,by simp,by simp⟩
  · rintro ⟨x,k,a,hx,rfl⟩
    exact ⟨map r x,c.residueLocalization_homogeneous resClass choice d hd x a k hx⟩

end GeneralizedEuler.Section4.SemiringGroupification.EulerCoordinates
