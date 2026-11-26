module

public import Section4.RVScissorRealization
public import Section4.TaggedLiftRealization
public import Mathlib.Algebra.Polynomial.Coeff

/-! Retain the degree in the realization of the RV scissor semiring.
The coefficient at each degree is an actual ungraded RV family class. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  (M : SortedStructure L E X) (S : SortedSubstructure M)

def realizeGradedScissors : RVSemiring M S →+* Polynomial (RVFamily.Classes M S) := by
  let f := RVFamily.realizeScissors M S
  let w (U : GradedObject M S) := Polynomial.monomial U.1 (f (objectClass M S U))
  apply descendWeights M S w
  intro a b rel
  have sound := congrArg f (scissors_sound M S rel)
  cases rel with
  | iso U V e =>
    change f (objectClass M S ⟨_,U⟩) = f (objectClass M S ⟨_,V⟩) at sound
    simp only [MvPolynomial.eval₂_X,w,sound]
  | zero U h =>
    have h0 : f (objectClass M S ⟨_,U⟩) = 0 := by
      simpa only [objectClass,map_zero] using sound
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_zero,w,h0,Polynomial.monomial_zero_right]
  | one U h =>
    have h1 : f (objectClass M S ⟨_,U⟩) = 1 := by
      simpa only [objectClass,map_one] using sound
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_one,w,h1,Polynomial.monomial_zero_left,map_one]
  | cut U V W A B hA hB disj cover eA eB =>
    have hc : f (objectClass M S ⟨_,U⟩) =
        f (objectClass M S ⟨_,V⟩) + f (objectClass M S ⟨_,W⟩) := by
      simpa only [objectClass,map_add] using sound
    simp only [MvPolynomial.eval₂_add,MvPolynomial.eval₂_X,w,hc,map_add]
  | prod U V W e =>
    have hp : f (objectClass M S ⟨_,W⟩) =
        f (objectClass M S ⟨_,U⟩) * f (objectClass M S ⟨_,V⟩) := by
      simpa only [objectClass,map_mul] using sound
    simp only [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,w,hp,Polynomial.monomial_mul_monomial]

theorem realizeGradedScissors_class (U : GradedObject M S) :
    realizeGradedScissors M S (objectClass M S U) =
      Polynomial.monomial U.1 (RVFamily.cls (RVFamily.single U.2.carrier U.2.definable)) := by
  unfold realizeGradedScissors
  rw [descendWeights_class,RVFamily.realizeScissors_class]

/-- Equal finite sums have the same RV family class in every degree. -/
theorem equal_graded_scissors_coefficients {I J : Type} [Fintype I] [Fintype J]
    (U : I → GradedObject M S) (V : J → GradedObject M S)
    (eq : ∑ i, objectClass M S (U i) = ∑ j, objectClass M S (V j)) (d : ℕ) :
    (∑ i, if (U i).1 = d then RVFamily.cls (RVFamily.single (U i).2.carrier (U i).2.definable) else 0) =
      (∑ j, if (V j).1 = d then RVFamily.cls (RVFamily.single (V j).2.carrier (V j).2.definable) else 0) := by
  have h := congrArg (fun x => (realizeGradedScissors M S x).coeff d) eq
  simpa only [map_sum,Polynomial.finsetSum_coeff,realizeGradedScissors_class,
    Polynomial.coeff_monomial] using h

/-- Collect the components of one degree as actual definable tagged
sets, keeping every component's original RV coordinates. -/
@[expose] def degreeFamily {I : Type} [Finite I] (U : I → GradedObject M S) (d : ℕ) :
    RVFamily M S where
  Tag := {i : I // (U i).1 = d}
  Coord i := Fin (U i.val).2.arity
  piece i := (U i.val).2.carrier
  definable i := (U i.val).2.definable

theorem degreeFamily_class {I : Type} [Fintype I] (U : I → GradedObject M S) (d : ℕ) :
    (degreeFamily M S U d).cls =
      ∑ i, if (U i).1 = d then RVFamily.cls (RVFamily.single (U i).2.carrier (U i).2.definable) else 0 := by
  classical
  let pred (i : I) := (U i).1 = d
  let w (i : I) := RVFamily.cls (RVFamily.single (U i).2.carrier (U i).2.definable)
  let : Fintype (degreeFamily M S U d).Tag := inferInstanceAs (Fintype {i : I // pred i})
  rw [RVFamily.cls_eq_sum]
  change (∑ i : {i : I // pred i}, w i.val) = ∑ i, if pred i then w i else 0
  have all : (Finset.univ : Finset {i : I // pred i}) = (Finset.univ : Finset I).subtype pred := by
    ext i
    simp
  rw [all,Finset.sum_subtype_eq_sum_filter,Finset.sum_filter]

/-- Equality of positive graded classes supplies a fixed-base isomorphism
on each degree, including the degree lowered by a zero blowup multiplier. -/
theorem equal_graded_scissors_degree_iso {I J : Type} [Fintype I] [Fintype J]
    (U : I → GradedObject M S) (V : J → GradedObject M S)
    (eq : ∑ i, objectClass M S (U i) = ∑ j, objectClass M S (V j)) (d : ℕ) :
    (degreeFamily M S U d).Iso (degreeFamily M S V d) := by
  apply (RVFamily.cls_eq_iff _ _).1
  rw [degreeFamily_class,degreeFamily_class]
  exact equal_graded_scissors_coefficients M S U V eq d

end GeneralizedEuler.Section5
