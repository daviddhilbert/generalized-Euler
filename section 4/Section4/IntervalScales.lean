module

public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic

/-! Convex subspaces associated to bounded interval widths in the
ordered vector space of values. All bounds use the field of exponents. -/
public section
namespace GeneralizedEuler.Section4
variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
  [Module F V] [IsOrderedModule F V]

def scaleSpace (a : V) : Submodule F V where
  carrier := {x | ∃ c : F, 0 ≤ c ∧ |x| ≤ c • |a|}
  zero_mem' := ⟨0,le_rfl,by simp⟩
  add_mem' := by
    rintro x y ⟨c,hc,hx⟩ ⟨d,hd,hy⟩
    exact ⟨c+d,add_nonneg hc hd,(abs_add_le _ _).trans ((add_le_add hx hy).trans_eq (add_smul c d |a|).symm)⟩
  smul_mem' := by
    rintro c x ⟨d,hd,hx⟩
    refine ⟨|c| * d,mul_nonneg (abs_nonneg _) hd,?_⟩
    rw [abs_smul,mul_smul]
    exact smul_le_smul_of_nonneg_left hx (abs_nonneg c)

theorem self_mem_scaleSpace (a : V) : a ∈ scaleSpace F a := ⟨1,zero_le_one,by simp⟩

theorem mem_scaleSpace_iff {x a : V} (ha : 0 < a) :
    x ∈ scaleSpace F a ↔ ∃ c : F, 0 < c ∧ |x| ≤ c • a := by
  constructor
  · rintro ⟨c,hc,hx⟩
    refine ⟨c+1,by positivity,?_⟩
    rw [abs_of_pos ha] at hx
    exact hx.trans (smul_le_smul_of_nonneg_right (by linarith) ha.le)
  · rintro ⟨c,hc,hx⟩
    exact ⟨c,hc.le,by simpa [abs_of_pos ha] using hx⟩

theorem scaleSpace_mono {a b : V} (h : a ∈ scaleSpace F b) : scaleSpace F a ≤ scaleSpace F b := by
  obtain ⟨d,hd,hab⟩ := h
  rintro x ⟨c,hc,hx⟩
  exact ⟨c*d,mul_nonneg hc hd,hx.trans ((smul_le_smul_of_nonneg_left hab hc).trans_eq (mul_smul c d |b|).symm)⟩

theorem scaleSpace_le_iff {a b : V} : scaleSpace F a ≤ scaleSpace F b ↔ a ∈ scaleSpace F b :=
  ⟨fun h => h (self_mem_scaleSpace F a),scaleSpace_mono F⟩

theorem scaleSpace_interval {a x : V} (hx : 0 ≤ x) (hxa : x ≤ a) : x ∈ scaleSpace F a :=
  ⟨1,zero_le_one,by simpa [abs_of_nonneg hx,abs_of_nonneg (hx.trans hxa)] using hxa⟩

theorem scaleSpace_convex {a x y z : V} (hx : x ∈ scaleSpace F a) (hz : z ∈ scaleSpace F a)
    (hxy : x ≤ y) (hyz : y ≤ z) : y ∈ scaleSpace F a := by
  obtain ⟨c,hc,hx⟩ := hx
  obtain ⟨d,hd,hz⟩ := hz
  refine ⟨max c d,hc.trans (le_max_left _ _), abs_le.mpr ⟨?_,?_⟩⟩
  · have l := hx.trans (smul_le_smul_of_nonneg_right (le_max_left c d) (abs_nonneg a))
    exact (abs_le.mp l).1.trans hxy
  · have r := hz.trans (smul_le_smul_of_nonneg_right (le_max_right c d) (abs_nonneg a))
    exact hyz.trans (abs_le.mp r).2

theorem larger_than_all_multiples {a b : V} (ha : 0 < a) (hb : 0 < b) :
    b ∉ scaleSpace F a ↔ ∀ c : F, 0 < c → c • a < b := by
  simp only [mem_scaleSpace_iff F ha,abs_of_pos hb,not_exists,not_and,not_le]

end GeneralizedEuler.Section4
