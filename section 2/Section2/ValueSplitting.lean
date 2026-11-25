module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective

/-! A section of the unsigned value map can be chosen to lift all base
values inside the base, as in the proof of Lemma 2.29. -/

public section

namespace GeneralizedEuler.Section2

variable {E G V : Type*} [Field E] [AddCommGroup G] [Module E G]
  [AddCommGroup V] [Module E V]

/-- A linear section that is compatible with a specified base subspace.
This includes the trivial base value group. -/
theorem exists_linearSection_preserving_base (v : G →ₗ[E] V)
    (hv : Function.Surjective v) (W : Submodule E G) :
    ∃ s : V →ₗ[E] G, v.comp s = LinearMap.id ∧
      ∀ a ∈ W.map v, s a ∈ W := by
  let R := W.map v
  let vr : W →ₗ[E] R :=
    (v.comp W.subtype).codRestrict R (fun w => Submodule.mem_map_of_mem w.property)
  have hvr : Function.Surjective vr := by
    intro a
    obtain ⟨x, hx, hxa⟩ := a.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  obtain ⟨sr, hsr⟩ := vr.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hvr)
  obtain ⟨p, hp⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
  obtain ⟨s0, hs0⟩ := v.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hv)
  have hsr' (a : R) : v (sr a : G) = (a : V) :=
    congrArg Subtype.val (DFunLike.congr_fun hsr a)
  have hp' (a : R) : p (a : V) = a := DFunLike.congr_fun hp a
  have hs0' (a : V) : v (s0 a) = a := DFunLike.congr_fun hs0 a
  let s : V →ₗ[E] G :=
    (W.subtype.comp sr).comp p + s0.comp (LinearMap.id - R.subtype.comp p)
  refine ⟨s, ?_, ?_⟩
  · ext a
    change v ((sr (p a) : G) + s0 (a - (p a : V))) = a
    rw [map_add, hsr', hs0', add_sub_cancel]
  · intro a ha
    let ar : R := ⟨a, ha⟩
    have hpa : p a = ar := hp' ar
    change (sr (p a) : G) + s0 (a - (p a : V)) ∈ W
    rw [hpa]
    have ha' : (ar : V) = a := rfl
    rw [ha', sub_self, map_zero, add_zero]
    exact (sr ar).property

end GeneralizedEuler.Section2
