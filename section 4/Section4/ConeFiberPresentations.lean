module

public import Section4.SimplicialValueFibers
public import Section4.TaggedBoxPresentations
import all Section4.SimplicialValueFibers
import all Section4.ValueScissors
import all Section4.DefinableValueFrames

/-! From a disjoint triangulation of a parameter fiber to a box
presentation of its signed tagged value class. The vertex matrices
have entries in the field of exponents and the translations lie in G. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject PaddedBox
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup V] [LinearOrder V]
  [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V] {J : Language} [J.Structure V]
  {G : Submodule F V} (L : BoxLanguage (J := J) G) (order : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})

structure FiberChart (G : Submodule F V) (k : ℕ) where
  fiber : ConeFiber G k
  rows : Fin k → fiber.Coeff → F
  shift : Fin k → G
  injective : InjOn (fun x j => (∑ i, rows j i • x i) + (shift j : V)) fiber.domain

namespace FiberChart
variable {k : ℕ} (c : FiberChart G k)
def eval (x : c.fiber.Coeff → V) (j : Fin k) := (∑ i, c.rows j i • x i) + (c.shift j : V)
def carrier := c.eval '' c.fiber.domain

include L in
omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem eval_definable : (G : Set V).DefinableMap J c.eval :=
  fun j => L.arithmetic.addFun (L.arithmetic.row (c.rows j)) (J.definableFun_const _ (c.shift j).property)

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
include L order in
theorem definable : (G : Set V).Definable J c.carrier :=
  image_of_map _ (c.eval_definable L) _ (c.fiber.domain_definable L order)

omit [IsStrictOrderedModule F V] in
theorem class_eq : pieceClass c.carrier (c.definable L order) =
    presentationValue L (⟨1,fun _ => c.fiber.axis,fun _ => c.fiber.axis_widths⟩ : Presentation G k) :=
  c.fiber.image_class L order c.eval (c.eval_definable L) c.injective

end FiberChart

def HasFiberTriangulation {k} (D : Set (Fin k → V)) : Prop :=
  ∃ (n : ℕ) (c : Fin n → FiberChart G k), Pairwise (fun i j => Disjoint (c i).carrier (c j).carrier) ∧
    (⋃ i, (c i).carrier) = D

omit [IsStrictOrderedModule F V] in
include order in
theorem box_presentation_of_triangulation {k} (D : Set (Fin k → V)) (hd : (G : Set V).Definable J D)
    (h : HasFiberTriangulation (G := G) D) : ∃ p : Presentation G k, presentationValue L p = pieceClass D hd := by
  obtain ⟨n,c,dj,rfl⟩ := h
  let p i : Presentation G k := ⟨1,fun _ => (c i).fiber.axis,fun _ => (c i).fiber.axis_widths⟩
  obtain ⟨q,eq⟩ := sum_presentations L p
  refine ⟨q,eq.trans ?_⟩
  rw [pieceClass_partition (fun i => (c i).carrier) (fun i => (c i).definable L order) dj]
  exact Finset.sum_congr rfl fun i _ => ((c i).class_eq L order).symm

end GeneralizedEuler.Section4
