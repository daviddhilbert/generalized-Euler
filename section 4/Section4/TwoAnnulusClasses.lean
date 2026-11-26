module

public import Section4.BoundedIntervalScissors
import all Section4.BoundedValueBoxes
import all Section4.BoundedIntervalScissors
import all Section4.ValueScissors

/-! Any product of two bounded intervals has the square of the unary
point as its groupified value class in the original degree two. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject SemiringGroupification
variable {F V : Type*} [Field F] [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V]
  {J : Language} [J.Structure V] (G : Submodule F V) (lang : ValueLanguage (J := J) G)

omit [IsOrderedAddMonoid V] in
theorem boundedBox_pair (a b : V) : boundedBox ![a,b] = cartesian (intervalPiece a) (intervalPiece b) := by
  ext x
  change (∀ i : Fin 2, 0 < x i ∧ x i < ![a,b] i) ↔ (0 < x 0 ∧ x 0 < a) ∧ (0 < x 1 ∧ x 1 < b)
  exact ⟨fun h => ⟨h 0,h 1⟩,fun h i => by fin_cases i; exact h.1; exact h.2⟩

include lang in
theorem bounded_pair_group_class (a b : V) (oa : a ∈ G) (ob : b ∈ G) (ha : 0 < a) (hb : 0 < b)
    (da : (G : Set V).Definable J (intervalPiece a)) (db : (G : Set V).Definable J (intervalPiece b))
    (dr : (G : Set V).Definable J (upperRay 0)) (dp : (G : Set V).Definable J ({0} : Set (Fin 1 → V)))
    (d : (G : Set V).Definable J (boundedBox ![a,b])) :
    of _ (pieceClass _ d) = (of _ (pieceClass {0} dp))^2 := by
  have cut : pieceClass _ d = pieceClass _ da * pieceClass _ db := by
    calc pieceClass _ d = pieceClass _ (cartesian_definable da db) := by congr 1; exact boundedBox_pair a b
         _ = _ := pieceClass_product da db
  rw [cut,map_mul,bounded_interval_group_class G lang a oa ha da dr dp,
    bounded_interval_group_class G lang b ob hb db dr dp,pow_two]
  exact neg_mul_neg (of _ (pieceClass {0} dp)) (of _ (pieceClass {0} dp))

end GeneralizedEuler.Section4
