module

public import Section4.ResidueMatrices
import all Section4.RelativeResidues

/-! Packing the two matrix components of a refinement into ambient-degree coordinates. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueFrame
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup T] [Module F T]
  {G : Submodule F V} {n r k m : ℕ} (A : ValueFrame G r n) (B : ValueFrame G k n)

theorem refinement_coordinates (idx : Fin m ≃ A.dependent) (α : Fin k → V)
    (hi : LinearIndependent F (G.mkQ ∘ α)) (h : B.eval α ∈ Set.range A.eval) :
    ∃ (L : Matrix A.dependent B.dependent F) (N : Matrix (Fin (m + (r-k))) B.dependent F),
      (∀ b : B.dependent → T, actRows L b = A.residuePart (B.padResidue b)) ∧
      Function.Bijective (actRows (T := T) N) ∧ ∀ D : Set (A.dependent → T),
        actRows N '' (actRows L ⁻¹' D) =
          {y : Fin (m + (r-k)) → T | y ∘ finSumFinEquiv ∘ Sum.inl ∘ idx.symm ∈ D} := by
  classical
  obtain ⟨L,R,e,spec,fst⟩ := A.refinement_matrices (T := T) B α hi h
  let N : Matrix (Fin (m + (r-k))) B.dependent F :=
    Sum.elim (L ∘ idx) R ∘ finSumFinEquiv.symm
  have left (x : B.dependent → T) (i : A.dependent) :
      actRows N x (finSumFinEquiv (Sum.inl (idx.symm i))) = (e x).1 i := by
    rw [spec]
    have row : N (finSumFinEquiv (Sum.inl (idx.symm i))) = L i := by
      unfold N
      rw [Function.comp_apply,Equiv.symm_apply_apply]
      change L (idx (idx.symm i)) = L i
      rw [idx.apply_symm_apply]
    exact Finset.sum_congr rfl (fun j _ => congrArg (· • x j) (congrFun row j))
  have right (x : B.dependent → T) (i : Fin (r-k)) :
      actRows N x (finSumFinEquiv (Sum.inr i)) = (e x).2 i := by
    rw [spec]; simp [actRows,N,Sum.elim,Function.comp_def]
  have recover (x : B.dependent → T) :
      e x = (actRows N x ∘ finSumFinEquiv ∘ Sum.inl ∘ idx.symm,actRows N x ∘ finSumFinEquiv ∘ Sum.inr) :=
    Prod.ext (funext fun i => (left x i).symm) (funext fun i => (right x i).symm)
  have surj (y : Fin (m+(r-k)) → T) : ∃ x, actRows N x = y := by
    obtain ⟨x,hx⟩ := e.surjective (y ∘ finSumFinEquiv ∘ Sum.inl ∘ idx.symm,y ∘ finSumFinEquiv ∘ Sum.inr)
    refine ⟨x,funext fun i => ?_⟩
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl i => simpa [hx] using left x (idx i)
    | inr j => exact (right x j).trans (congrFun (congrArg Prod.snd hx) j)
  refine ⟨L,N,fun b => (congrArg Prod.fst (spec b)).symm.trans (fst b),⟨?_,surj⟩,?_⟩
  · intro x y eq; apply e.injective
    rw [recover x,recover y,eq]
  · intro D
    ext y
    have core (x : B.dependent → T) :
        actRows N x ∘ finSumFinEquiv ∘ Sum.inl ∘ idx.symm = actRows L x :=
      (congrArg Prod.fst (recover x)).symm.trans (congrArg Prod.fst (spec x))
    constructor
    · rintro ⟨x,hx,rfl⟩
      change _ ∘ _ ∘ _ ∘ _ ∈ D
      rwa [core]
    · intro hy
      obtain ⟨x,rfl⟩ := surj y
      exact ⟨x,show actRows L x ∈ D by rw [← core x]; exact hy,rfl⟩

end GeneralizedEuler.Section4.ValueFrame
