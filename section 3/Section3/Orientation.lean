module

public import Section2.ResidueOrder
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Basic

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

open scoped Topology

omit [IsStrictOrderedRing K] in
/-- Remark 3.29 at a nonsingular point. Entrywise continuity of the
Jacobian yields a neighborhood with the same strict determinant sign. -/
theorem locally_constant_jacobian_sign {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] [TopologicalSpace K] [OrderTopology K] [IsTopologicalRing K]
    (J : X → Matrix ι ι K) {a : X} (hc : ContinuousAt J a) (hn : (J a).det ≠ 0) :
    (∀ᶠ x in 𝓝 a, 0 < (J x).det) ∨ (∀ᶠ x in 𝓝 a, (J x).det < 0) := by
  have hd : ContinuousAt (fun x => (J x).det) a :=
    continuous_id.matrix_det.continuousAt.comp hc
  rcases lt_or_gt_of_ne hn with h | h
  · exact Or.inr (hd.tendsto.eventually_lt_const h)
  · exact Or.inl (hd.tendsto.eventually_const_lt h)

set_option linter.style.haveILetI false in
/-- Corollary 3.33 on the regular good labels. Reducing the integral
Jacobian matrix entrywise reduces its determinant. A nonzero reduced
determinant detects both signs of the field determinant. -/
theorem jacobian_sign_of_residue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι O) (R : Matrix ι ι (Residue O))
    (hJ : ∀ i j, IsLocalRing.residue O (J i j) = R i j) (hn : R.det ≠ 0) :
    letI := residueLinearOrder O hO
    (0 < (J.det : K) ↔ 0 < R.det) ∧ ((J.det : K) < 0 ↔ R.det < 0) := by
  letI := residueLinearOrder O hO
  have hm : J.map (IsLocalRing.residue O) = R := Matrix.ext hJ
  have he : IsLocalRing.residue O J.det = R.det := by rw [RingHom.map_det, ← hm]; rfl
  have hpos := residue_lt_residue_iff O hO (x := 0) (y := J.det)
  have hneg := residue_lt_residue_iff O hO (x := J.det) (y := 0)
  rw [map_zero, he, and_iff_left hn.symm] at hpos
  rw [map_zero, he, and_iff_left hn] at hneg
  exact ⟨hpos.symm,hneg.symm⟩

end GeneralizedEuler.Section3
