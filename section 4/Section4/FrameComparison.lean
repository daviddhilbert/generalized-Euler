module

public import Section4.RectangleDecomposition
import all Section4.ValueFrames
import all Section4.PositiveRectangles

/-! Rigidity at an independent point and the geometry of common refinements. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open scoped BigOperators Matrix
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {G : Submodule F V} {n r k : ℕ}

theorem affine_rows_rigid {I : Type*} [Fintype I] (α : I → V)
    (hi : LinearIndependent F (G.mkQ ∘ α)) (c d : I → F) (u w : G)
    (eq : (∑ i, c i • α i) + u.val = (∑ i, d i • α i) + w.val) : c = d ∧ u = w := by
  have h := congrArg G.mkQ eq
  simp only [map_add,map_sum,map_smul,
    show G.mkQ u.val = 0 from (Submodule.Quotient.mk_eq_zero G).mpr u.property,
    show G.mkQ w.val = 0 from (Submodule.Quotient.mk_eq_zero G).mpr w.property,add_zero] at h
  have cd := funext (Fintype.linearIndependent_iffₛ.mp hi c d h)
  subst d
  exact ⟨rfl,Subtype.ext (add_left_cancel eq)⟩

namespace ValueFrame
variable (A : ValueFrame G r n) (B : ValueFrame G k n)

/-- Project the fine affine expression onto the coarse free coordinates. -/
def projectedRows : Matrix (Fin r) (Fin k) F := fun i => B.rows (A.free i)
def projectedShift : Fin r → G := B.shift ∘ A.free

theorem eval_project (z : Fin k → V) : B.eval z ∘ A.free =
    actRows (A.projectedRows B) z + fun i => ((A.projectedShift B) i).val := by funext i; rfl

theorem eval_project_twice (z : Fin k → V) (i : Fin n) :
    A.eval (B.eval z ∘ A.free) i = actRows (A.rows * A.projectedRows B) z i +
      (actRows A.rows (A.projectedShift B) i + A.shift i : G).val := by
  rw [A.eval_project B z,actRows_mul]
  simp [eval,actRows,smul_add,Finset.sum_add_distrib,add_assoc]

/-- A single independent point in a fine cell forces all the affine
identities for containment of its entire affine hull. -/
theorem refinement_equations (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) :
    B.rows = A.rows * A.projectedRows B ∧
    B.shift = actRows A.rows (A.projectedShift B) + A.shift := by
  obtain ⟨γ,hγ⟩ := h
  have hfree : B.eval α ∘ A.free = γ := hγ ▸ A.project_eval γ
  have he : B.eval α = A.eval (B.eval α ∘ A.free) := by rw [hfree,hγ]
  have each (i) := congrFun he i
  have both (i) := affine_rows_rigid α hi (B.rows i) ((A.rows * A.projectedRows B) i)
    (B.shift i) (actRows A.rows (A.projectedShift B) i + A.shift i)
    ((each i).trans (A.eval_project_twice B α i))
  exact ⟨funext fun i => (both i).1,funext fun i => (both i).2⟩

theorem refinement_rank (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) : k ≤ r := by
  obtain ⟨rows,_⟩ := A.refinement_equations B α hi h
  let C := A.projectedRows B
  let q : Matrix (Fin k) (Fin r) F := fun i => A.rows (B.free i)
  have inv : q * C = 1 := by
    ext i j
    exact (congrFun (congrFun rows (B.free i)) j).symm.trans (B.freeRow i j)
  have inj : Function.Injective C.mulVecLin := by
    intro x y e
    have l := congrArg q.mulVecLin e
    change q *ᵥ (C *ᵥ x) = q *ᵥ (C *ᵥ y) at l
    simpa only [Matrix.mulVec_mulVec,inv,Matrix.one_mulVec] using l
  simpa using LinearMap.finrank_le_finrank_of_injective inj

/-- The geometric degree loss on refining a value cell is nonnegative.
If ranks coincide then projections give the inverse changes of coordinates. -/
theorem refinement_hull (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) (z : Fin k → V) :
    A.eval (B.eval z ∘ A.free) = B.eval z := by
  obtain ⟨rows,shift⟩ := A.refinement_equations B α hi h
  funext i
  rw [A.eval_project_twice B z i,← rows]
  exact congrArg (fun t : G => actRows B.rows z i + t.val) (congrFun shift i).symm

end ValueFrame
end GeneralizedEuler.Section4
