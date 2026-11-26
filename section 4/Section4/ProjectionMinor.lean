module

public import Section4.GraphProjection
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Choosing free coordinates entirely within an injective graph projection. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F : Type*} [Field F] {k r : ℕ}

theorem full_rank_minor (A : Matrix (Fin k) (Fin r) F) (h : Function.Injective A.mulVecLin) :
    ∃ (p : Fin r ↪ Fin k) (U : (Matrix (Fin r) (Fin r) F)ˣ), ∀ i, U.val i = A (p i) := by
  classical
  have dim : Module.finrank F (Submodule.span F (Set.range A.row)) = r := by
    rw [← A.rank_eq_finrank_span_row]
    change Module.finrank F (LinearMap.range A.mulVecLin) = r
    simpa using (LinearEquiv.ofInjective A.mulVecLin h).finrank_eq.symm
  obtain ⟨f,mem,_,ind⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range A.row)
  let e := finCongr dim
  let row i := f (e.symm i)
  have hi : LinearIndependent F row := ind.comp _ e.symm.injective
  choose p hp using fun i : Fin r => mem (e.symm i)
  have pinj : Function.Injective p := by
    intro i j eq; apply hi.injective
    exact (hp i).symm.trans ((congrArg A.row eq).trans (hp j))
  let C : Matrix (Fin r) (Fin r) F := fun i => A (p i)
  have eq : C.row = row := funext hp
  obtain ⟨U,hU⟩ := Matrix.linearIndependent_row_iff_isUnit.mp (eq ▸ hi)
  exact ⟨⟨p,pinj⟩,U,fun i => congrFun hU i⟩

end GeneralizedEuler.Section4
