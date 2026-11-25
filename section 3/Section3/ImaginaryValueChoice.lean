module

public import Section3.TupleValueParameters
public import Section3.DiscGraphImages
public import Mathlib.Algebra.Order.Hom.Monoid
import all Section3.ValueChoice
import all Section3.Atomicity

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

variable {K : Type*} [Field K] (O : ValuationSubring K)
  [DenselyOrdered O.ValueGroup] [NoMaxOrder O.ValueGroup]

private theorem fixed_infimum {Γ I : Type*} [LinearOrder Γ] (e : I → Γ ≃o Γ) {B : Set Γ} {r : Γ}
    (inf : IsGLB B r) (stable : ∀ i t, e i t ∈ B ↔ t ∈ B) (i : I) : e i r = r := by
  have he : (e i) '' B = B := by
    ext t
    obtain ⟨s,rfl⟩ := (e i).surjective t
    exact (e i).injective.mem_set_image.trans (stable i s).symm
  have h := (e i).isGLB_image'.mpr inf
  rw [he] at h
  exact h.unique inf

/-- Canonical unary value choice in a form valid for imaginary bases.
Only the nontrivial value step has to be fixed. No field representative
of the step or of the parameter codes is fixed by the automorphisms. -/
theorem invariant_value_in_set {I : Type*} (e : I → O.ValueGroup ≃*o O.ValueGroup)
    (step : O.ValueGroup) (large : 1 < step) (stepFix : ∀ i, e i step = step)
    (square : ∀ t : O.ValueGroup, ∃ q, q*q = t)
    {S : Set O.ValueGroup} (ne : S.Nonempty) (stable : ∀ i t, e i t ∈ S ↔ t ∈ S)
    (cells : ∃ C : Finset (Set O.ValueGroup), (∀ T ∈ C, IsUnaryCell T) ∧ S = ⋃ T ∈ C, T)
    (gaps : ∀ a : O.ValueGroup, ∃ C : Finset (Set O.ValueGroup), (∀ T ∈ C, IsUnaryCell T) ∧ Ioi a \ S = ⋃ T ∈ C, T) :
    ∃ t ∈ S, ∀ i, e i t = t := by
  obtain ⟨a,low,mem | ⟨b,lt,first⟩⟩ := firstValueInterval_of_cells ne cells
  · exact ⟨a,mem,fixed_infimum (fun i => (e i).toOrderIso) low stable⟩
  have fixA := fixed_infimum (fun i => (e i).toOrderIso) low stable
  let B := Ioi a \ S
  have upper : ∃ c > a, Ioo a c ⊆ S ∧ ∀ i, e i c = c := by
    by_cases hn : B.Nonempty
    · obtain ⟨c,hc,_⟩ := firstValueInterval_of_cells hn (gaps a)
      have bl : b ∈ lowerBounds B := fun z hz => le_of_not_gt (fun h => hz.2 (first ⟨hz.1,h⟩))
      refine ⟨c,lt.trans_le (hc.2 bl),fun z hz => by_contra (fun no => hz.2.not_ge (hc.1 (show z ∈ B from ⟨hz.1,no⟩))),?_⟩
      apply fixed_infimum (fun i => (e i).toOrderIso) hc
      intro i z
      change (a < e i z ∧ e i z ∉ S) ↔ a < z ∧ z ∉ S
      have bound : a < e i z ↔ a < z := by
        calc a < e i z ↔ e i a < e i z := by rw [show e i a = a from fixA i]
             _ ↔ _ := (e i).toOrderIso.lt_iff_lt
      exact bound.and (not_congr (stable i z))
    · have tail : Ioi a ⊆ S := fun z hz => by_contra (fun no => hn ⟨z,hz,no⟩)
      by_cases az : a = 0
      · exact ⟨step,az ▸ zero_lt_one.trans large,fun _ h => tail h.1,stepFix⟩
      · refine ⟨a*step,by simpa using mul_lt_mul_of_pos_left large (pos_iff_ne_zero.mpr az),fun _ h => tail h.1,fun i => ?_⟩
        rw [map_mul,stepFix,show e i a = a from fixA i]
  obtain ⟨c,ac,inside,fixC⟩ := upper
  by_cases az : a = 0
  · have cp : 0 < c := az ▸ ac
    have sp := zero_lt_one.trans large
    refine ⟨c/step,inside ⟨az ▸ div_pos cp sp, (div_lt_iff₀ sp).mpr (by simpa using mul_lt_mul_of_pos_left large cp)⟩,fun i => ?_⟩
    change (e i).toMulEquiv (c/step) = _
    rw [map_div₀]; change e i c / e i step = _; rw [fixC,stepFix]
  · obtain ⟨q,hq⟩ := square (a*c)
    have ap := pos_iff_ne_zero.mpr az
    refine ⟨q,inside ⟨by
      by_contra! h; exact (mul_lt_mul_of_pos_left ac ap).not_ge (hq ▸ mul_le_mul' h h),by
      by_contra! h; exact (mul_lt_mul_of_pos_right ac (ap.trans ac)).not_ge (hq ▸ mul_le_mul' h h)⟩,fun i => ?_⟩
    have h := congrArg (e i) hq
    rw [map_mul,map_mul,show e i a = a from fixA i,fixC,←hq] at h
    exact le_antisymm (le_of_not_gt (fun ne => (mul_self_lt_mul_self zero_le ne).ne h.symm))
      (le_of_not_gt (fun ne => (mul_self_lt_mul_self zero_le ne).ne h))

/-- Adding a value parameter preserves all tests on an atom, for any
collection of sorts or imaginary coordinates. The family R represents
an arbitrary formula over the old base. The conclusion compares its
truth at the given value without naming a representative. -/
theorem atomic_tests_with_value {X I : Type*} (A : Set X) (move : I → X ≃ X)
    (pres : ∀ i x, move i x ∈ A ↔ x ∈ A) (trans : ∀ x ∈ A, ∀ y ∈ A, ∃ i, move i x = y)
    (value : I → O.ValueGroup ≃*o O.ValueGroup) (step : O.ValueGroup) (hs : 1 < step)
    (fixed : ∀ i, value i step = step) (square : ∀ t : O.ValueGroup, ∃ q, q*q = t)
    (R : X → O.ValueGroup → Prop) (equiv : ∀ i x v, R (move i x) (value i v) ↔ R x v)
    (cells : ∀ B : Set O.ValueGroup, (B = {s | (∃ x ∈ A, R x s) ∧ ∃ y ∈ A, ¬R y s} ∨
       ∃ a, B = Ioi a \ {s | (∃ x ∈ A, R x s) ∧ ∃ y ∈ A, ¬R y s}) →
      ∃ C : Finset (Set O.ValueGroup), (∀ T ∈ C, IsUnaryCell T) ∧ B = ⋃ T ∈ C, T) :
    ∀ v x, x ∈ A → ∀ y ∈ A, R x v ↔ R y v := by
  let B := {s | (∃ x ∈ A, R x s) ∧ ∃ y ∈ A, ¬R y s}
  have stable i v : value i v ∈ B ↔ v ∈ B := by
    constructor
    · rintro ⟨⟨x,hx,yes⟩,y,hy,no⟩
      obtain ⟨a,rfl⟩ := (move i).surjective x
      obtain ⟨b,rfl⟩ := (move i).surjective y
      exact ⟨⟨a,(pres i a).mp hx,(equiv i a v).mp yes⟩,b,(pres i b).mp hy,fun h => no ((equiv i b v).mpr h)⟩
    · rintro ⟨⟨x,hx,yes⟩,y,hy,no⟩
      exact ⟨⟨move i x,(pres i x).mpr hx,(equiv i x v).mpr yes⟩,move i y,(pres i y).mpr hy,fun h => no ((equiv i y v).mp h)⟩
  have empty : ¬ B.Nonempty := by
    intro ne
    obtain ⟨v,⟨⟨x,hx,yes⟩,y,hy,no⟩,fixV⟩ := invariant_value_in_set O value step hs fixed square ne stable
      (cells _ (Or.inl rfl)) (fun a => cells _ (Or.inr ⟨a,rfl⟩))
    obtain ⟨i,hit⟩ := trans x hx y hy
    have out := (equiv i x v).mpr yes
    exact no (by rwa [hit,fixV] at out)
  intro v x hx y hy
  exact ⟨fun h => by_contra (fun no => empty ⟨v,⟨x,hx,h⟩,y,hy,no⟩),
    fun h => by_contra (fun no => empty ⟨v,⟨y,hy,h⟩,x,hx,no⟩)⟩

end GeneralizedEuler.Section3
