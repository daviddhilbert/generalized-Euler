module

public import Section4.SemiringGroupification
public import Section4.RectangleRange
import all Section4.Factors

/-! Groupification of the concrete rectangle presentation. The residue
Euler polynomial acts on the groupified value factor by evaluating X at
minus the degree-one point. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Polynomial
open scoped TensorProduct
namespace SemiringGroupification
variable {R V T : Type*} [CommSemiring R] [CommSemiring V] [CommSemiring T]
  (r : R →+* T) (v : V →+* T) (t : R) (e : V) (balance : r t = v e)
  (χ : R →+* Polynomial ℤ) (line : χ t = -X)

def residueEvaluation : R →+* Ring V := (eval₂RingHom (Int.castRingHom (Ring V)) (-(of V e))).comp χ

include line in
theorem residueEvaluation_line : residueEvaluation e χ t = of V e := by
  change Polynomial.eval₂ _ _ (χ t) = _
  rw [line]
  change (eval₂RingHom (Int.castRingHom (Ring V)) (-(of V e))) (-X) = _
  rw [map_neg,coe_eval₂RingHom,eval₂_X,neg_neg]

variable (bij : Function.Bijective (rectangleHom r v t e balance))

def rectangleRetraction : Ring T →+* Ring V :=
  let forward := RingEquiv.ofBijective (rectangleHom r v t e balance) bij
  let back := rectangleHom (residueEvaluation e χ) (of V) t e (residueEvaluation_line t e χ line)
  lift (back.comp forward.symm.toRingHom)

include bij line in
theorem rectangleRetraction_product (a : R) (b : V) :
    rectangleRetraction r v t e balance χ line bij (of T (r a * v b)) = residueEvaluation e χ a * of V b := by
  let :=  (Polynomial.eval₂RingHom (Nat.castRingHom R) t).toAlgebra
  let :=  (Polynomial.eval₂RingHom (Nat.castRingHom V) e).toAlgebra
  let forward := RingEquiv.ofBijective (rectangleHom r v t e balance) bij
  have eq : forward (a ⊗ₜ[Polynomial ℕ] b) = r a * v b := rectangleHom_pure r v t e balance a b
  unfold rectangleRetraction
  rw [lift_of]
  change (rectangleHom (residueEvaluation e χ) (of V) t e (residueEvaluation_line t e χ line)) (forward.symm (r a * v b)) = _
  rw [← eq,forward.symm_apply_apply]
  exact rectangleHom_pure (residueEvaluation e χ) (of V) t e (residueEvaluation_line t e χ line) a b

include bij line in
theorem groupified_value_retracts : (rectangleRetraction r v t e balance χ line bij).comp (map v) = RingHom.id (Ring V) := by
  apply hom_ext; intro b
  change rectangleRetraction _ _ _ _ _ _ _ _ (map v (of V b)) = of V b
  rw [map_of]
  simpa only [map_one,one_mul] using rectangleRetraction_product r v t e balance χ line bij 1 b

include bij line in
theorem groupified_value_map_injective : Function.Injective (map v) := by
  have left : Function.LeftInverse (rectangleRetraction r v t e balance χ line bij) (map v) :=
    fun b => DFunLike.congr_fun (groupified_value_retracts r v t e balance χ line bij) b
  exact left.injective

include bij line in
theorem rectangleRetraction_homogeneous (a : R) (b : V) (i : ℕ) (z : ℤ) (ha : χ a = C z * X^i) :
    rectangleRetraction r v t e balance χ line bij (of T (r a * v b)) =
      (-1 : Ring V)^i * (z : Ring V) * (of V e)^i * of V b := by
  rw [rectangleRetraction_product]
  congr 1
  change eval₂ (Int.castRingHom _) (-(of V e)) (χ a) = _
  rw [ha,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
  change (z : Ring V) * (-(of V e))^i = _
  rw [_root_.neg_pow (of V e) i]; ring

include line balance in
/-- The residue classification in Remark 4.8 makes the residue Euler
polynomial an isomorphism after groupification. It then suffices to compare
the two ring maps on X, which is represented by the negative unit-line class. -/
private theorem residueEvaluation_recovers (resClass : Function.Bijective (lift χ)) (a : R) :
    map v (residueEvaluation e χ a) = of T (r a) := by
  let iso := RingEquiv.ofBijective (lift χ) resClass
  let ev := eval₂RingHom (Int.castRingHom (Ring V)) (-(of V e))
  let m := (map v).comp ev
  let n := (map r).comp iso.symm.toRingHom
  have gen : iso (-(of R t)) = X := by
    rw [map_neg]; change -(lift χ (of R t)) = X
    rw [lift_of,line,neg_neg]
  have eq : m = n := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change map v (ev X) = map r (iso.symm X)
      rw [← gen,iso.symm_apply_apply]
      rw [gen]; change map v (eval₂ _ _ X) = _
      rw [eval₂_X,map_neg,map_neg,map_of,map_of,balance]
  have ha : iso (of R a) = χ a := lift_of _ _
  have h := DFunLike.congr_fun eq (χ a)
  change map v (residueEvaluation e χ a) = map r (iso.symm (χ a)) at h
  rw [← ha,iso.symm_apply_apply,map_of] at h
  exact h

include bij line in
theorem groupified_value_map_bijective (resClass : Function.Bijective (lift χ)) : Function.Bijective (map v) := by
  refine ⟨groupified_value_map_injective r v t e balance χ line bij,?_⟩
  let back := rectangleRetraction r v t e balance χ line bij
  have identity : (map v).comp back = RingHom.id (Ring T) := by
    apply hom_ext; intro x
    let :=  (Polynomial.eval₂RingHom (Nat.castRingHom R) t).toAlgebra
    let :=  (Polynomial.eval₂RingHom (Nat.castRingHom V) e).toAlgebra
    let D := rectangleHom r v t e balance
    obtain ⟨p,rfl⟩ := bij.surjective x
    change map v (back (of T (D p))) = of T (D p)
    induction p using TensorProduct.inductionOn with
    | tmul a b =>
      have hp : D (a ⊗ₜ[Polynomial ℕ] b) = r a * v b := rectangleHom_pure r v t e balance a b
      rw [hp]; change map v (rectangleRetraction _ _ _ _ _ _ _ _ _) = _
      rw [rectangleRetraction_product,map_mul,residueEvaluation_recovers r v t e balance χ line resClass,map_of,map_mul]
    | add p q hp hq => simp only [map_add,hp,hq]
  exact fun y => ⟨back y,DFunLike.congr_fun identity y⟩

end SemiringGroupification
end GeneralizedEuler.Section4
