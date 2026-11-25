module

public import Section3.Orientation
public import Section2.TorsorDerivative
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set Filter Matrix
open scoped Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [OrderTopology K] {n m : ℕ}

/-- The coordinate partial is taken in the order topology of the field.
The empty list stores the map, and prepending a coordinate differentiates
the partial indexed by the tail in that coordinate. -/
structure OrderJetOn (f : (Fin n → K) → Fin m → K) (p : ℕ)
    (U : Set (Fin n → K)) where
  entry : List (Fin n) → (Fin n → K) → Fin m → K
  base : entry [] = f
  continuous : ∀ w, w.length ≤ p → ContinuousOn (entry w) U
  derivative : ∀ w, w.length < p → ∀ x ∈ U, ∀ i j,
    HasOrderDerivativeAt (fun t => entry w (Function.update x i t) j)
      (x i) (entry (i :: w) x j)

def OrderJetOn.jacobian {f : (Fin n → K) → Fin m → K} {p U} (J : OrderJetOn f p U)
    (x : Fin n → K) : Matrix (Fin m) (Fin n) K := fun j i => J.entry [i] x j

/-- Remark 3.29. Continuity at the point is sufficient at order zero.
Positive orders require a smooth neighborhood and full rank at the point. -/
def regularLocus (f : (Fin n → K) → Fin m → K) : ℕ → Set (Fin n → K)
  | 0 => {x | ContinuousAt f x}
  | p + 1 => {x | ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ J : OrderJetOn f (p+1) U,
      (J.jacobian x).rank = min n m}

omit [IsStrictOrderedRing K] [OrderTopology K] in
@[simp] theorem mem_regularLocus_zero (f : (Fin n → K) → Fin m → K) (x : Fin n → K) :
    x ∈ regularLocus f 0 ↔ ContinuousAt f x := Iff.rfl

omit [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
theorem square_rank_iff_det_ne_zero (M : Matrix (Fin n) (Fin n) K) :
    M.rank = n ↔ M.det ≠ 0 := by
  suffices M.rank = Fintype.card (Fin n) ↔ M.det ≠ 0 by simpa using this
  rw [← Matrix.mulVec_surjective_iff_rank_eq_card,
    Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

omit [OrderTopology K] in
theorem OrderJetOn.jacobian_unique {f : (Fin n → K) → Fin m → K} {U V p q}
    (J : OrderJetOn f (p+1) U) (H : OrderJetOn f (q+1) V) {x} (hx : x ∈ U) (hy : x ∈ V) :
    J.jacobian x = H.jacobian x := by
  ext j i
  have hJ := J.derivative [] (by simp) x hx i j
  have hH := H.derivative [] (by simp) x hy i j
  rw [J.base] at hJ
  rw [H.base] at hH
  exact hJ.unique hH

omit [IsStrictOrderedRing K] in
/-- A single jet works on the entire neighborhood. Its Jacobian is
intrinsic wherever another jet is available, by jacobian_unique. -/
theorem square_regular_neighborhood [IsTopologicalRing K]
    {f : (Fin n → K) → Fin n → K} {p x} (hx : x ∈ regularLocus f (p+1)) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ J : OrderJetOn f (p+1) U,
      ∀ᶠ y in 𝓝 x, y ∈ regularLocus f (p+1) ∧
        (0 < (J.jacobian x).det ↔ 0 < (J.jacobian y).det) := by
  obtain ⟨U,hU,hxU,J,hr⟩ := hx
  have hdet := (square_rank_iff_det_ne_zero _).mp (by simpa using hr)
  have hc : ContinuousAt J.jacobian x := by
    apply continuousAt_pi.mpr
    intro j
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_apply j).continuousAt.comp
      ((J.continuous [i] (by simp) x hxU).continuousAt (hU.mem_nhds hxU))
  refine ⟨U,hU,hxU,J,?_⟩
  have hs := locally_constant_jacobian_sign J.jacobian hc hdet
  have within (y) (hy : y ∈ U) (hn : (J.jacobian y).det ≠ 0) :
      y ∈ regularLocus f (p+1) :=
    ⟨U,hU,hy,J,by simpa using (square_rank_iff_det_ne_zero _).mpr hn⟩
  rcases hs with pos | neg
  · filter_upwards [hU.mem_nhds hxU,pos] with y hy hpos
    exact ⟨within y hy hpos.ne', iff_of_true pos.self_of_nhds hpos⟩
  · filter_upwards [hU.mem_nhds hxU,neg] with y hy hneg
    exact ⟨within y hy hneg.ne, iff_of_false neg.self_of_nhds.not_gt hneg.not_gt⟩

end GeneralizedEuler.Section3
