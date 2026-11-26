module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Algebra.Group.Basic

/-! The coordinate transposition used in the relatively unary
factorization of Lemma 5.24. -/

public section

namespace GeneralizedEuler.Section5

variable {I K : Type*} [AddCommGroup K] [DecidableEq I]

/-- A coordinate map is relatively unary in `i` if all the other field
coordinates are fixed. The definition allows any source and target tags. -/
@[expose] def RelativelyUnary {A B : Type*} (i : I) (f : (I → K) × A → (I → K) × B) : Prop :=
  ∀ x j, j ≠ i → (f x).1 j = x.1 j

/-- Add another coordinate. Its inverse subtracts that same, unchanged
coordinate. -/
def addCoordinate (i j : I) (h : j ≠ i) : (I → K) ≃ (I → K) where
  toFun x := Function.update x i (x i + x j)
  invFun x := Function.update x i (x i - x j)
  left_inv x := by
    funext s
    by_cases hs : s = i
    · subst s
      simp only [Function.update_self,Function.update_of_ne h, add_sub_cancel_right]
    · simp only [Function.update_of_ne hs]
  right_inv x := by
    funext s
    by_cases hs : s = i
    · subst s
      simp only [Function.update_self,Function.update_of_ne h, sub_add_cancel]
    · simp only [Function.update_of_ne hs]

/-- Reflect one coordinate about half of another, expressed without
division. -/
def reflectCoordinate (i j : I) (h : j ≠ i) : (I → K) ≃ (I → K) where
  toFun x := Function.update x i (x j - x i)
  invFun x := Function.update x i (x j - x i)
  left_inv x := by
    funext s
    by_cases hs : s = i
    · subst s
      simp only [Function.update_self,Function.update_of_ne h, sub_sub_cancel]
    · simp only [Function.update_of_ne hs]
  right_inv x := by
    funext s
    by_cases hs : s = i
    · subst s
      simp only [Function.update_self,Function.update_of_ne h, sub_sub_cancel]
    · simp only [Function.update_of_ne hs]

/-- The three changes used to exchange coordinates. With any carried
tags the same maps act only on one field coordinate at each step. -/
theorem transposition_by_relatively_unary {A : Type*} (i j : I) (h : i ≠ j) :
    let F := fun f : (I → K) ≃ (I → K) => fun x : (I → K) × A => (f x.1,x.2)
    RelativelyUnary i (F (addCoordinate i j h.symm)) ∧
      RelativelyUnary j (F (reflectCoordinate j i h)) ∧
      RelativelyUnary i (F (addCoordinate i j h.symm).symm) ∧
      ∀ x : I → K, (addCoordinate i j h.symm).symm
        (reflectCoordinate j i h (addCoordinate i j h.symm x)) =
          x ∘ Equiv.swap i j := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x s hs
    exact Function.update_of_ne hs _ _
  · intro x s hs
    exact Function.update_of_ne hs _ _
  · intro x s hs
    exact Function.update_of_ne hs _ _
  · intro x
    funext s
    let y := Function.update x i (x i + x j)
    let z := Function.update y j (y i - y j)
    change Function.update z i (z i - z j) s = (x ∘ Equiv.swap i j) s
    by_cases hi : s = i
    · subst s
      simp only [z, y, Function.update_self, Function.update_of_ne h, Function.update_of_ne h.symm,
        add_sub_cancel_right, add_sub_cancel_left, Function.comp_apply, Equiv.swap_apply_left]
    · by_cases hj : s = j
      · subst s
        simp only [z, y, Function.update_self, Function.update_of_ne h, Function.update_of_ne h.symm,
          add_sub_cancel_right, Function.comp_apply, Equiv.swap_apply_right]
      · simp only [z, y, Function.update_of_ne hi, Function.update_of_ne hj, Function.comp_apply,
          Equiv.swap_apply_of_ne_of_ne hi hj]

end GeneralizedEuler.Section5
