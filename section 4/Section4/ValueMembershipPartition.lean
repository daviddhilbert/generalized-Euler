module

public import Section4.CommonValueRefinement
import all Section4.ValueStratification

/-! Disjoint simultaneous refinement for overlapping projected graph supports. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {J : Language} [J.Structure V]
  {G : Submodule F V} {n : ℕ} {I : Type} [Fintype I]

theorem stratify_memberships (lang : ValueLanguage (J := J) G)
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set V).Definable J D))
    (A : I → Set (Fin n → V)) (ha : ∀ i, (G : Set V).Definable J (A i)) :
    ∃ (l : ℕ) (p : Fin l → DefinablePiece J G n) (active : Fin l → I → Bool),
      (∀ γ, ∃! t, γ ∈ (p t).support) ∧
      ∀ t i γ, γ ∈ (p t).support → (γ ∈ A i ↔ active t i = true) := by
  classical
  let C (b : I → Bool) := ⋂ i, if b i then A i else (A i)ᶜ
  have cut (b : I → Bool) : (G : Set V).Definable J (C b) := by
    apply Set.definable_iInter_of_finite
    intro i
    cases b i <;> simp only [Bool.false_eq_true,↓reduceIte] <;> first | exact ha i | exact (ha i).compl
  have member (b : I → Bool) (γ) : γ ∈ C b ↔ ∀ i, (γ ∈ A i ↔ b i = true) := by
    unfold C
    rw [Set.mem_iInter]
    apply forall_congr'; intro i; cases b i <;> simp
  choose count cell cover using fun b => stratify_values _ (fun p D i => lang.cut p D i) sat _ (cut b)
  let idx := (Fintype.equivFin (Σ b, Fin (count b))).symm
  let p t := cell (idx t).1 (idx t).2
  have spec (t) {γ} (h : γ ∈ (p t).support) := (member _ γ).mp ((cover (idx t).1 γ).1.mpr ⟨(idx t).2,h⟩)
  refine ⟨_,p,fun t => (idx t).1,?_,fun t i γ h => spec t h i⟩
  intro γ
  let b (i : I) := decide (γ ∈ A i)
  have hb : γ ∈ C b := (member b γ).mpr (fun i => by simp [b])
  obtain ⟨j,hj⟩ := (cover b γ).1.mp hb
  refine ⟨idx.symm ⟨b,j⟩,?_,?_⟩
  · change γ ∈ (cell (idx (idx.symm ⟨b,j⟩)).1 (idx (idx.symm ⟨b,j⟩)).2).support
    rw [idx.apply_symm_apply]; exact hj
  · intro t ht; apply idx.injective
    rw [idx.apply_symm_apply]
    have same : (idx t).1 = b := by
      funext i
      exact Bool.eq_iff_iff.mpr ((spec t ht i).symm.trans ((member b γ).mp hb i))
    obtain ⟨c,u,eq⟩ : ∃ c u, idx t = ⟨c,u⟩ := ⟨_,_,rfl⟩
    change γ ∈ (cell (idx t).1 (idx t).2).support at ht
    rw [eq] at same ht ⊢; change c = b at same
    subst c
    exact congrArg (Sigma.mk b) ((cover b γ).2 _ _ ht hj)

end GeneralizedEuler.Section4
