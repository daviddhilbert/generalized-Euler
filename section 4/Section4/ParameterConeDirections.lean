module

public import Section4.PolyhedralProjectionTests
import all Section4.PolyhedralProjectionTests
import all Section4.ProjectedConeRays
import all Section4.PointedConeSubdivision
import all Section4.SimplicialConeSubdivision
import all Section4.LinearSignTransfer

/-! A sign-compatible parameter simplex gives every perturbation used
in the extreme-ray lemma, also on its proper faces. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {E P : Type*} [AddCommGroup E] [Module F E] [AddCommGroup P] [Module F P]
variable (c : SimpleCone F P)

/-- On the closed simplex each test is everywhere weakly positive or
everywhere weakly negative. -/
def Compatible (forms : Finset (P →ₗ[F] F)) := ∀ a ∈ forms,
  (∀ j, 0≤a (c.ray j)) ∨ (∀ j, a (c.ray j)≤0)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem SimpleCone.expand {P : Type*} [AddCommGroup P] [Module F P] (c : SimpleCone F P)
    (x : Fin c.rays → F) : c.param x = ∑ i, x i • c.ray i := by
  have eq : (∑ i, x i • Pi.single i (1 : F)) = x := by
    funext j
    rw [Finset.sum_apply,Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [Pi.single_eq_of_ne (Ne.symm hi)]
    · simp
  conv_lhs => rw [← eq]
  simp [SimpleCone.ray,map_sum]

private theorem nonnegative_sign (a : P →ₗ[F] F) (nonneg : ∀ j, 0≤a (c.ray j))
    (x y : Fin c.rays → F) (px : ∀ j, 0≤x j) (py : ∀ j, 0≤y j) (support : ∀ j, 0<x j ↔ 0<y j) :
    SameSign (a (c.param x)) (a (c.param y)) := by
  have sum (z : Fin c.rays → F) : a (c.param z) = ∑ i, z i * a (c.ray i) := by rw [c.expand]; simp [map_sum]
  have pos (z) (hz : ∀ j, 0≤z j) : 0<a (c.param z) ↔ ∃ i, 0<z i ∧ 0<a (c.ray i) := by
    rw [sum,Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hz i) (nonneg i))]
    simp only [Finset.mem_univ,true_and]
    apply exists_congr
    intro i
    rw [mul_pos_iff]; simp [(hz i).not_gt,(nonneg i).not_gt]
  have posEq : 0<a (c.param x) ↔ 0<a (c.param y) :=
    (pos x px).trans ((exists_congr (fun i => and_congr_left' (support i))).trans (pos y py).symm)
  exact ⟨iff_of_true ((sum x).symm ▸ Finset.sum_nonneg (fun i _ => mul_nonneg (px i) (nonneg i)))
    ((sum y).symm ▸ Finset.sum_nonneg (fun i _ => mul_nonneg (py i) (nonneg i))),by simpa using posEq.not⟩

theorem compatible_signs {forms} (comp : Compatible c forms) (x y : Fin c.rays → F)
    (px : ∀ j, 0≤x j) (py : ∀ j, 0≤y j) (support : ∀ j, 0<x j ↔ 0<y j)
    (a) (ha : a ∈ forms) : SameSign (a (c.param x)) (a (c.param y)) := by
  rcases comp a ha with pos|neg
  · exact nonnegative_sign c a pos x y px py support
  · have h := nonnegative_sign c (-a) (fun i => neg_nonneg.mpr (neg i)) x y px py support
    exact ⟨by simpa using h.2,by simpa using h.1⟩

def overParameter : (E × (Fin c.rays → F)) →ₗ[F] E × P := LinearMap.prodMap LinearMap.id c.param

variable {I : Type*} [Fintype I] (a : I → (E × P) →ₗ[F] F)
local notation "π" => LinearMap.snd F E P

omit [Fintype I] in
theorem parameter_directions {forms : Finset (P →ₗ[F] F)} (comp : Compatible c forms)
    (adapted : ∀ u, Controlled forms (π '' activeFace a u))
    (u : E × (Fin c.rays → F)) (inside : overParameter c u ∈ polyCone a) (positive : ∀ i, 0≤u.2 i)
    (i : Fin c.rays) (hi : 0<u.2 i) : ∃ w : E × (Fin c.rays → F),
      (∀ t, a t (overParameter c u)=0 → a t (overParameter c w)=0) ∧ w.2=Pi.single i 1 := by
  let t := u.2 + Pi.single i (1 : F)
  have pos (j) : 0≤t j := by by_cases h : j=i <;> simp [t,h,positive,(positive i).trans (le_add_of_nonneg_right zero_le_one)]
  have support (j) : 0<u.2 j ↔ 0<t j := by
    by_cases h : j=i
    · subst j; exact iff_of_true hi (by simpa [t] using add_pos hi (zero_lt_one : (0:F)<1))
    · simp [t,h]
  have mem : c.param u.2 ∈ π '' activeFace a (overParameter c u) := ⟨overParameter c u,⟨inside,fun _ h => h⟩,rfl⟩
  have target := (adapted _ _ _ (compatible_signs c comp u.2 t positive pos support)).mp mem
  obtain ⟨z,hz,im⟩ := target
  let v : E × (Fin c.rays → F) := (z.1,t)
  have ev : overParameter c v = z := Prod.ext rfl im.symm
  refine ⟨v-u,fun j h => ?_,?_⟩
  · rw [map_sub,ev,map_sub,h,(hz.2 j h),sub_zero]
  · change u.2 + Pi.single i (1 : F) - u.2 = _
    abel

end GeneralizedEuler.Section4.Polyhedral
