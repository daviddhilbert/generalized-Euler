module

public import Mathlib.Tactic
/-! Dimension and Euler characteristic for the residue classes of Remark 4.8. -/

public section
namespace GeneralizedEuler.Section4

inductive ResidueClass
  | empty
  | inhabited (dimension : ℕ) (euler : ℤ) (finite_pos : dimension = 0 → 0 < euler)
  deriving DecidableEq

namespace ResidueClass

def chi : ResidueClass → ℤ
  | empty => 0
  | inhabited _ a _ => a

def degreeLE (k : ℕ) : ResidueClass → Prop
  | empty => True
  | inhabited d _ _ => d ≤ k

instance : Zero ResidueClass := ⟨empty⟩
instance : One ResidueClass := ⟨inhabited 0 1 (by decide)⟩
instance : Add ResidueClass where
  add
    | empty, x | x, empty => x
    | inhabited i a hi, inhabited j b hj =>
      inhabited (max i j) (a + b) (fun h => by
        have := hi (by omega); have := hj (by omega); omega)
instance : Mul ResidueClass where
  mul
    | empty, _ | _, empty => empty
    | inhabited i a hi, inhabited j b hj =>
      inhabited (i+j) (a*b) (fun h => mul_pos (hi (by omega)) (hj (by omega)))

@[simp] theorem empty_add (x : ResidueClass) : empty + x = x := by cases x <;> rfl
@[simp] theorem add_empty (x : ResidueClass) : x + empty = x := by cases x <;> rfl
@[simp] theorem empty_mul (x : ResidueClass) : empty * x = empty := by cases x <;> rfl
@[simp] theorem mul_empty (x : ResidueClass) : x * empty = empty := by cases x <;> rfl
@[simp] theorem add_inhabited (i a hi j b hj) :
    inhabited i a hi + inhabited j b hj = inhabited (max i j) (a+b)
      (fun h => by have := hi (by omega); have := hj (by omega); omega) := rfl
@[simp] theorem mul_inhabited (i a hi j b hj) :
    inhabited i a hi * inhabited j b hj = inhabited (i+j) (a*b)
      (fun h => mul_pos (hi (by omega)) (hj (by omega))) := rfl

instance : CommSemiring ResidueClass where
  zero_add := empty_add
  add_zero := add_empty
  one_mul x := by change inhabited 0 1 _ * x = x; cases x <;> simp
  mul_one x := by change x * inhabited 0 1 _ = x; cases x <;> simp
  zero_mul := empty_mul
  mul_zero := mul_empty
  add_comm x y := by cases x <;> cases y <;> simp [max_comm, add_comm]
  add_assoc x y z := by cases x <;> cases y <;> cases z <;> simp [max_assoc, add_assoc]
  mul_comm x y := by cases x <;> cases y <;> simp [add_comm, mul_comm]
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> simp [add_assoc, mul_assoc]
  left_distrib x y z := by
    cases x <;> cases y <;> cases z <;> simp [Nat.add_max_add_left, mul_add]
  right_distrib x y z := by
    cases x <;> cases y <;> cases z <;> simp [Nat.add_max_add_right, add_mul]
  nsmul := nsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl

def eulerHom : ResidueClass →+* ℤ where
  toFun := chi
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by cases x <;> cases y <;> simp [chi]
  map_mul' x y := by cases x <;> cases y <;> simp [chi]

theorem degree_add {k x y} (hx : degreeLE k x) (hy : degreeLE k y) :
    degreeLE k (x+y) := by
  cases x <;> cases y <;> simp_all [degreeLE]

theorem degree_mul {k l x y} (hx : degreeLE k x) (hy : degreeLE l y) :
    degreeLE (k+l) (x*y) := by
  cases x <;> cases y <;> simp_all [degreeLE]; omega

/-- The precise additive groupification relation in each ambient degree. -/
theorem stably_equal_iff {k x y} (hx : degreeLE k x) (hy : degreeLE k y) :
    (∃ z, degreeLE k z ∧ x + z = y + z) ↔ chi x = chi y := by
  constructor
  · rintro ⟨z,_,hz⟩
    have he := congrArg eulerHom hz
    rw [map_add, map_add] at he
    exact add_right_cancel he
  · intro h
    refine ⟨inhabited k 1 (fun _ => by decide), le_rfl, ?_⟩
    cases x <;> cases y <;> simp_all [degreeLE, chi]

end ResidueClass
end GeneralizedEuler.Section4
