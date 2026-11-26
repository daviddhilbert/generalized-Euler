module

public import Section5.BlowupCongruence
public import Mathlib.Data.List.Perm.Basic

/-! The adjacent-exchange and relatively unary chain arguments in the
positive-degree kernel proof. -/

public section

namespace GeneralizedEuler.Section5

variable {I C : Type*} (equivClass : C → C → Prop) (he : Equivalence equivClass)

include he in
/-- Comparison after an arbitrary common prefix is sufficient for
independence of the entire contraction order. -/
theorem contraction_order_of_adjacent_exchange
    (contract : List I → C)
    (exchange : ∀ pre post i j,
      equivClass (contract (pre ++ i :: j :: post)) (contract (pre ++ j :: i :: post)))
    {a b : List I} (order : a.Perm b) :
    equivClass (contract a) (contract b) := by
  suffices h : ∀ pre, equivClass (contract (pre ++ a)) (contract (pre ++ b)) from h []
  induction order with
  | nil => intro pre; exact he.refl _
  | cons i _ ih =>
    intro pre
    simpa only [List.append_assoc,List.singleton_append] using ih (pre ++ [i])
  | swap i j post =>
    intro pre
    exact exchange pre post j i
  | trans _ _ ih₁ ih₂ =>
    intro pre
    exact he.trans (ih₁ pre) (ih₂ pre)

variable {F : Type*} (unaryArrow : F → F → Prop)

include he in
/-- Use an admissible contraction order at each relatively unary arrow
and order independence at its two endpoints. -/
theorem contraction_class_along_unary_chain
    (canonical : F → C) (chosen : F → List I → C)
    (compareOrder : ∀ a order, equivClass (canonical a) (chosen a order))
    (compareUnary : ∀ a b, unaryArrow a b →
      ∃ order, equivClass (chosen a order) (chosen b order))
    {a b : F} (chain : Relation.ReflTransGen unaryArrow a b) :
    equivClass (canonical a) (canonical b) := by
  induction chain with
  | refl => exact he.refl _
  | @tail x y _ hxy ih =>
    obtain ⟨order,eq⟩ := compareUnary x y hxy
    exact he.trans ih (he.trans (compareOrder x order) (he.trans eq (he.symm (compareOrder y order))))

end GeneralizedEuler.Section5
