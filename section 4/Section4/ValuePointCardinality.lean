module

public import Section4.DegreeZeroInclusion
public import Section4.ResidueClasses
import all Section4.ResidueClasses
import all Section4.ValueDescent
import all Section4.ValueScissors

/-! Cardinality of ordinary value sets in every degree. A singleton can
never equal two tagged singletons together with a third summand. This
detects the obstruction to an additive splitting before groupification. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject

variable {V : Type*} {J : Language} [J.Structure V] (A : Set V)

def valueCardinalityMeasure : PieceMeasure J A ℕ∞ where
  weight D _ := D.encard
  empty _ := Set.encard_empty
  one := by simp
  cut _ _ _ _ disj := Set.encard_union_eq disj
  iso _ _ _ _ e _ := ENat.card_congr e
  prod D E _ _ := (ENat.card_congr (cartesianEquiv D E).symm).trans (ENat.card_prod _ _)

def valueCardinality : SemiringOfSets (J := J) A →+* ℕ∞ :=
  (valueCardinalityMeasure (J := J) A).descend

@[simp] theorem valueCardinality_piece {k} (D : Set (Fin k → V)) (h : A.Definable J D) :
    valueCardinality A (pieceClass D h) = D.encard :=
  (valueCardinalityMeasure A).descend_piece D h

theorem value_singleton_ne_double_add {k} (x : Fin k → V) (hx : A.Definable J {x})
    (c : SemiringOfSets (J := J) A) : pieceClass {x} hx ≠ pieceClass {x} hx + pieceClass {x} hx + c := by
  intro eq
  have count := congrArg (valueCardinality (J := J) A) eq
  simp only [map_add,valueCardinality_piece,Set.encard_singleton] at count
  have le : (1 : ℕ∞) + 1 ≤ 1 := (le_self_add : 1 + 1 ≤ 1 + 1 + valueCardinality A c).trans count.ge
  norm_num at le

/-- It suffices that a proposed additive map return the value singleton
on its lift. No additive zero or multiplication law is needed. -/
theorem no_additive_splitting_of_line_cut {R : Type*} [AddSemigroup R]
    {k} (x : Fin k → V) (hx : A.Definable J {x}) (line point : R)
    (cut : line = line + line + point) (r : R → SemiringOfSets (J := J) A)
    (add : ∀ a b, r (a + b) = r a + r b) :
    r line ≠ pieceClass {x} hx := by
  intro h
  have eq := congrArg r cut
  rw [add,add,h] at eq
  exact value_singleton_ne_double_add A x hx _ eq

/-- In the residue dimension–Euler classification exactly the
Euler-zero classes coincide with their own double. -/
theorem ResidueClass.double_eq_iff_euler_zero (x : ResidueClass) :
    x + x = x ↔ x.chi = 0 := by
  cases x with
  | empty => simp [ResidueClass.chi]
  | inhabited d a h => simp [ResidueClass.chi]

end GeneralizedEuler.Section4
