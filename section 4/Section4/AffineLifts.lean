module

public import Section2.PositiveRVMonomials
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

/-! Positive leading terms are written additively as a module over the field of
exponents (Section 2). Matrix action is the product of named powers in RV. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
open scoped BigOperators
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T]
  [AddCommGroup V] [Module F V]
variable {i j k : Type*} [Fintype i] [Fintype j] [Fintype k]

@[expose] def actRows (A : Matrix j i F) (x : i → T) (r : j) : T := ∑ c, A r c • x c

omit [Fintype j] in
theorem actRows_map (v : T →ₗ[F] V) (A : Matrix j i F) (x : i → T) :
    v ∘ actRows A x = actRows A (v ∘ x) := by
  funext r
  simp [actRows]

omit [Fintype k] in
theorem actRows_mul (B : Matrix k j F) (A : Matrix j i F) (x : i → T) :
    actRows (B * A) x = actRows B (actRows A x) := by
  funext r
  simp only [actRows, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem actRows_one [DecidableEq i] (x : i → T) : actRows (1 : Matrix i i F) x = x := by
  funext r
  simp [actRows, Matrix.one_apply, ite_smul]

/-- The inverse subtracts the representative of the intercept before applying
the inverse matrix. -/
def affineLift [DecidableEq i] (A : (Matrix i i F)ˣ) (u : i → T) : (i → T) ≃ (i → T) where
  toFun x := actRows A.val x + u
  invFun y := actRows A.inv (y - u)
  left_inv x := by simp only [add_sub_cancel_right, ← actRows_mul, A.inv_val, actRows_one]
  right_inv y := by simp only [← actRows_mul, A.val_inv, actRows_one, sub_add_cancel]

theorem affineLift_value [DecidableEq i] (v : T →ₗ[F] V) (A : (Matrix i i F)ˣ)
    (u x : i → T) : v ∘ (affineLift A u x) = affineLift A (v ∘ u) (v ∘ x) := by
  funext r
  exact (map_add v _ _).trans (congrArg (· + v (u r)) (congrFun (actRows_map v A.val x) r))

theorem exists_base_affineLift [DecidableEq i] (v : T →ₗ[F] V) (W : Submodule F T)
    (A : (Matrix i i F)ˣ) (δ : i → V) (h : ∀ r, δ r ∈ W.map v) :
    ∃ u : i → W, ∀ x, v ∘ affineLift A (fun r => (u r).val) x = affineLift A δ (v ∘ x) := by
  choose t ht he using h
  refine ⟨fun r => ⟨t r, ht r⟩, fun x => ?_⟩
  rw [affineLift_value]
  exact congrArg (fun b => affineLift A b (v ∘ x)) (funext he)

/-- Coordinates for a full pullback over an affine graph. The second component
of each normalized tuple lies in the residue kernel. -/
def graphChart (v : T →ₗ[F] V) (A : Matrix j i F) (u : j → T) (D : Set (i → V)) :
    {p : (i → T) × (j → T) // v ∘ p.1 ∈ D ∧ v ∘ p.2 = actRows A (v ∘ p.1) + v ∘ u} ≃
      {z : i → T // v ∘ z ∈ D} × (j → v.ker) where
  toFun p := (⟨p.1.1,p.2.1⟩, fun r => ⟨p.1.2 r - (actRows A p.1.1 r + u r), by
    change v _ = 0
    rw [map_sub, map_add, ← Function.comp_apply (f := v) (g := actRows A p.1.1),
      actRows_map]
    exact sub_eq_zero.mpr (congrFun p.2.2 r)⟩)
  invFun q := ⟨(q.1.val, fun r => (q.2 r).val + (actRows A q.1.val r + u r)), q.1.property, by
    funext r
    change v ((q.2 r).val + _) = _
    rw [map_add, (q.2 r).property, zero_add, map_add]
    exact congrArg (· + v (u r)) (congrFun (actRows_map v A q.1.val) r)⟩
  left_inv p := by apply Subtype.ext; exact Prod.ext rfl (funext fun r => sub_add_cancel _ _)
  right_inv q := by
    refine Prod.ext ?_ ?_
    · rfl
    funext r
    exact Subtype.ext (add_sub_cancel_right _ _)

end GeneralizedEuler.Section4
