module

public import Section4.HomogeneousValueLift
public import Section4.GeometricValueInclusion
import all Section4.HomogeneousValueLift
import all Section4.ResidueClasses

/-! The Euler and cardinality steps of Corollary 4.22a, in the positive
semiring and the groupified balanced rectangle presentation. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject Polynomial

theorem duplicate_residue_not_injective {V T : Type*} [CommSemiring T]
    {J : Language} [J.Structure V] (A : Set V) (lift : SemiringOfSets (J := J) A →+* T)
    {k} (p : Fin k → V) (hp : A.Definable J {p}) (u : T) (duplicate : u + u = u) :
    ¬ Function.Injective (fun y : homogeneousValue (J := J) A k => u * lift y.val) := by
  intro inj
  let e := homogeneousPiece A _ hp
  have eq : u * lift e.val = u * lift (e+e).val := by
    change _ = u * lift (e.val + e.val)
    rw [map_add,mul_add,← add_mul,duplicate]
  have same := congrArg Subtype.val (inj eq)
  apply value_singleton_ne_double_add A p hp 0
  change pieceClass {p} hp = pieceClass {p} hp + pieceClass {p} hp at same
  simpa using same

theorem euler_zero_residue_not_injective {V T : Type*} [CommSemiring T]
    {J : Language} [J.Structure V] (A : Set V) (lift : SemiringOfSets (J := J) A →+* T)
    {k} (p : Fin k → V) (hp : A.Definable J {p}) {R : Type*} [AddMonoid R]
    (res : R →+ T) (u : R) (classify : R →+ ResidueClass) (classInj : Function.Injective classify)
    (zero : (classify u).chi = 0) :
    ¬ Function.Injective (fun y : homogeneousValue (J := J) A k => res u * lift y.val) := by
  apply duplicate_residue_not_injective A lift p hp
  rw [← map_add]
  apply congrArg res
  apply classInj
  rw [map_add]
  exact (ResidueClass.double_eq_iff_euler_zero _).mpr zero

namespace SemiringGroupification
variable {R V T : Type*} [CommSemiring R] [CommSemiring V] [CommSemiring T]
  (r : R →+* T) (v : V →+* T) (t : R) (e : V) (balance : r t = v e)
  (χ : R →+* Polynomial ℤ) (line : χ t = -X) (bij : Function.Bijective (rectangleHom r v t e balance))

include balance line bij in
theorem cancel_residue_euler (u : R) (x y : V) (i : ℕ) (z : ℤ) (hz : z ≠ 0)
    (poly : χ u = C z * X^i) (eq : r u * v x = r u * v y)
    (ψ : Ring V →+* ℤ) (point : ψ (of V e) = 1) : ψ (of V x) = ψ (of V y) := by
  let ρ := rectangleRetraction r v t e balance χ line bij
  have h := congrArg (fun a => ψ (ρ (of T a))) eq
  change ψ (ρ (of T (r u * v x))) = ψ (ρ (of T (r u * v y))) at h
  dsimp only [ρ] at h
  rw [rectangleRetraction_homogeneous _ _ _ _ _ _ _ _ _ _ _ _ poly,
      rectangleRetraction_homogeneous _ _ _ _ _ _ _ _ _ _ _ _ poly] at h
  simp only [map_mul,map_pow,map_neg,map_one,map_intCast,point,one_pow,mul_one] at h
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero i (by decide : (-1 : ℤ) ≠ 0)) hz) h

end SemiringGroupification
end GeneralizedEuler.Section4
