module

public import Section5.RelativeUnaryShears
public import Mathlib.Logic.Equiv.Set

/-! The induction step in a relatively unary factorization. After
one output coordinate determines the remaining field output over the
fixed input coordinates, the intermediate bijection records it. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

variable {I K R T : Type*} [DecidableEq I]
  {A : Set ((I → K) × R)} {B : Set ((I → K) × T)}

@[expose] def recordOutputCoordinate (i j : I) (f : A → B) (x : A) : (I → K) × T :=
  (Function.update x.val.1 i ((f x).val.1 j),(f x).val.2)

theorem recordOutputCoordinate_fixes (i j : I) (f : A → B) (x : A) (k : I) (h : k ≠ i) :
    (recordOutputCoordinate i j f x).1 k = x.val.1 k :=
  Function.update_of_ne h _ _

theorem recordOutputCoordinate_injective (i j : I) (e : A ≃ B)
    (determines : ∀ x y : A, (∀ k, k ≠ i → x.val.1 k = y.val.1 k) →
      (e x).val.1 j = (e y).val.1 j → (e x).val.1 = (e y).val.1) :
    Function.Injective (recordOutputCoordinate i j e) := by
  intro x y eq
  have heads (k : I) (hk : k ≠ i) : x.val.1 k = y.val.1 k := by
    have h := congrFun (congrArg Prod.fst eq) k
    rwa [recordOutputCoordinate_fixes i j e x k hk,recordOutputCoordinate_fixes i j e y k hk] at h
  have lead : (e x).val.1 j = (e y).val.1 j := by
    have h := congrFun (congrArg Prod.fst eq) i
    simpa only [recordOutputCoordinate,Function.update_self] using h
  have ht := congrArg (fun p : (I → K) × T => p.2) eq
  have tags : (e x).val.2 = (e y).val.2 := ht
  exact e.injective (Subtype.ext (Prod.ext (determines x y heads lead) tags))

@[expose] def swapFieldCoordinates (i j : I) : ((I → K) × T) ≃ ((I → K) × T) where
  toFun x := (x.1 ∘ Equiv.swap i j,x.2)
  invFun x := (x.1 ∘ Equiv.swap i j,x.2)
  left_inv x := Prod.ext (funext fun k => congrArg x.1 (Equiv.swap_apply_self i j k)) rfl
  right_inv x := Prod.ext (funext fun k => congrArg x.1 (Equiv.swap_apply_self i j k)) rfl

/-- The first map is relatively unary in `i`. After aligning the chosen
output coordinate with `i`, the remaining map fixes that coordinate. -/
theorem factor_at_recovered_coordinate (i j : I) (e : A ≃ B)
    (determines : ∀ x y : A, (∀ k, k ≠ i → x.val.1 k = y.val.1 k) →
      (e x).val.1 j = (e y).val.1 j → (e x).val.1 = (e y).val.1) :
    let F := Set.range (recordOutputCoordinate i j e)
    let G := swapFieldCoordinates i j '' B
    ∃ (first : A ≃ F) (tail : F ≃ G),
      (∀ x : A, (first x).val = recordOutputCoordinate i j e x) ∧
      (∀ x : F, (tail x).val.1 i = x.val.1 i) ∧
      ∀ x : A, (tail (first x)).val = swapFieldCoordinates i j (e x).val := by
  intro F G
  let a : A ≃ F := Equiv.ofInjective (recordOutputCoordinate i j e)
    (recordOutputCoordinate_injective i j e determines)
  let b : B ≃ G := Equiv.Set.image _ _ (swapFieldCoordinates i j).injective
  let tail := a.symm.trans (e.trans b)
  have evaluate (x : A) : (tail (a x)).val = swapFieldCoordinates i j (e x).val := by
    change (b (e (a.symm (a x)))).val = _
    rw [a.symm_apply_apply]
    rfl
  refine ⟨a,tail,fun _ => rfl,?_,evaluate⟩
  intro x
  obtain ⟨y,rfl⟩ := a.surjective x
  rw [evaluate]
  change (e y).val.1 (Equiv.swap i j i) =
    Function.update y.val.1 i ((e y).val.1 j) i
  rw [Equiv.swap_apply_left,Function.update_self]

end GeneralizedEuler.Section5
