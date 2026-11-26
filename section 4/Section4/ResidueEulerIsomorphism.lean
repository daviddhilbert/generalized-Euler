module

public import Section4.GradedEulerMaps
public import Section4.ResidueCancellation
import all Section4.GradedEulerMaps
import all Section4.ResidueScissors
import all Section4.SemiringGroupification
import all Section4.Factors

/-! From the positive dimension--Euler classification of Remark 4.8
to the polynomial isomorphism on the actual residue groupification. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 Polynomial SemiringGroupification GradedEuler
set_option backward.isDefEq.respectTransparency false
variable {J : Language} {F Γ : Type*} {Z : TCsort → Type*} {M : SortedStructure J F Z}
  {S : SortedSubstructure M} (v : Z .rv → Γ)

local notation "R" => ResidueSemiring M S v

def residueDegree (k : ℕ) : AddSubmonoid R where
  carrier := {x | polynomialMeasure _ _ (residue_homogeneous M S v) (RingHom.id R) x=Polynomial.C x*X^k}
  zero_mem' := by simp
  add_mem' := by rintro x y hx hy; change _ = _ at hx hy ⊢; rw [map_add,hx,hy,map_add,add_mul]

theorem residueDegree_class {k} (U : RVObject M S k) (hu : U.IsResidue M S v) : residueClass U hu∈residueDegree v k :=
  polynomialMeasure_X _ _ (residue_homogeneous M S v) (RingHom.id R) ⟨⟨k,U⟩,hu⟩

theorem residueDegree_power (p : R) (hp : p ∈ residueDegree v 1) (k : ℕ) : p^k ∈ residueDegree v k := by
  change polynomialMeasure _ _ _ _ p = C p * X^1 at hp
  change polynomialMeasure _ _ _ _ (p^k) = _
  rw [map_pow,hp,pow_one,mul_pow,map_pow]

/-- The external o-minimal classification in each positive semigroup.
The degree bound includes the empty class. -/
structure ResidueEulerClassification (ordinary : R →+* ℤ) where
  classify : ∀ k, residueDegree v k →+ ResidueClass
  injective : ∀ k, Function.Injective (classify k)
  range : ∀ k, Set.range (classify k) = {x | x.degreeLE k}
  euler : ∀ k (x : residueDegree v k), (classify k x).chi=ordinary x.val

namespace ResidueEulerClassification
variable {v} {ordinary : ResidueSemiring M S v →+* ℤ} (c : ResidueEulerClassification v ordinary)
include c

theorem stable {k} (x y : residueDegree v k) (same : ordinary x.val=ordinary y.val) :
    of R x.val=of R y.val := by
  have le (w : residueDegree v k) : (c.classify k w).degreeLE k := by
    change c.classify k w ∈ {a | a.degreeLE k}
    rw [← c.range]; exact ⟨w,rfl⟩
  obtain ⟨u,hu,eq⟩ := (ResidueClass.stably_equal_iff (le x) (le y)).mpr ((c.euler k x).trans (same.trans (c.euler k y).symm))
  obtain ⟨z,rfl⟩ := show u ∈ Set.range (c.classify k) from (c.range k).symm ▸ hu
  have plus : x+z=y+z := c.injective k (by simpa only [map_add] using eq)
  exact add_right_cancel (show of R x.val + of R z.val = of R y.val + of R z.val by
    simpa only [AddSubmonoid.coe_add,map_add] using congrArg (fun a : residueDegree v k => of R a.val) plus)

theorem zero_double {k} (x : residueDegree v k) (zero : ordinary x.val=0) : x+x=x := by
  apply c.injective k
  rw [map_add]
  exact (ResidueClass.double_eq_iff_euler_zero _).mpr ((c.euler k x).trans zero)

variable (p : ResidueSemiring M S v) (hp : p∈residueDegree v 1) (one : ordinary p=1)
include hp one in
theorem group_class {k} (x : residueDegree v k) : of R x.val = (ordinary x.val : SemiringGroupification.Ring R) * (of R p)^k := by
  let a := ordinary x.val
  let q : residueDegree v k := ⟨p^k,residueDegree_power v p hp k⟩
  let s := a.toNat
  let t := (-a).toNat
  have sub : (s : ℤ) - (t : ℤ) = a := by dsimp [s,t]; omega
  have same : ordinary (x+t • q).val = ordinary (s • q).val := by
    change ordinary (x.val+t • p^k) = ordinary (s • p^k)
    simp only [nsmul_eq_mul,map_add,map_mul,map_natCast,map_pow,one,one_pow,mul_one]
    change a + t = s
    omega
  have eq := c.stable (x+t • q) (s • q) same
  change of R (x.val+t • p^k) = of R (s • p^k) at eq
  simp only [nsmul_eq_mul,map_add,map_mul,map_natCast,map_pow] at eq
  change of R x.val = (a : SemiringGroupification.Ring R) * _
  rw [← sub,Int.cast_sub,Int.cast_natCast,Int.cast_natCast]
  linear_combination eq

include hp one in
theorem polynomial_bijective (point : polynomialMeasure _ _ (residue_homogeneous M S v) ordinary p = X) :
    Function.Bijective (GradedEuler.residue M S v ordinary) := by
  let f := GradedEuler.residue M S v ordinary
  let back := eval₂RingHom (Int.castRingHom (SemiringGroupification.Ring R)) (of R p)
  have right : f.comp back = RingHom.id (Polynomial ℤ) := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change f (eval₂ _ _ X) = X
      rw [eval₂_X]; exact (lift_of _ _).trans point
  have left : back.comp f = RingHom.id (SemiringGroupification.Ring R) := by
    apply hom_ext
    have identity : (back.comp f).comp (of R) = of R := by
      let proj := (ringConGen (residueRelation M S v)).mk'
      have eq : ((back.comp f).comp (of R)).comp proj = (of R).comp proj := by
        apply MvPolynomial.ringHom_ext
        · intro n
          rw [show MvPolynomial.C n = (n : MvPolynomial _ ℕ) from map_natCast _ n,map_natCast,map_natCast]
        · rintro ⟨⟨k,U⟩,hu⟩
          change back (f (of R (residueClass U hu))) = of R (residueClass U hu)
          rw [show f (of R (residueClass U hu)) = _ from GradedEuler.residue_class M S v ordinary U hu]
          rw [map_mul,map_pow]
          simp only [back,coe_eval₂RingHom,eval₂_C,eval₂_X,Int.coe_castRingHom]
          exact (c.group_class p hp one ⟨_,residueDegree_class v U hu⟩).symm.trans rfl
      apply RingHom.ext; intro x
      obtain ⟨t,rfl⟩ := (ringConGen (residueRelation M S v)).mk'_surjective x
      exact DFunLike.congr_fun eq t
    exact fun x => DFunLike.congr_fun identity x
  exact ⟨fun x y eq => (DFunLike.congr_fun left x).symm.trans ((congrArg back eq).trans (DFunLike.congr_fun left y)),
    fun z => ⟨back z,DFunLike.congr_fun right z⟩⟩

end ResidueEulerClassification
end GeneralizedEuler.Section4
