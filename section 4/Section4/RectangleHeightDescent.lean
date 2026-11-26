module

public import Section4.RectangleWeightPresentations
public import Section4.CanonicalObjectWeights
import all Section4.RVScissorRealization
import all Section4.NormalRectangleCover
import all Section4.NormalRectangles
import all Section4.TaggedLiftRealization
import all Section4.RVFamilyOperations
import all Section4.FiniteScissors
import all Section4.ValuePadding
import all Section4.ResidueProducts

/-! Descent of the height invariant to the graded RV semiring. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k : ℕ}
variable (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
open scoped TensorProduct
open ValueObject
variable {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)


local notation "M" => canonicalStructure (L := J) O hO P
local notation "Rect" => NormalRectangle (JG := JG) (G := G) O v hO P S
open RVFamily



namespace RectangleWeight
local notation "Wt" => RectangleWeight pull hv res val (C := C)

def descend (unique : ∀ {k a x y}, Wt k a x → Wt k a y → x=y)
  (total : ∀ (U : GradedObject M S), ∃ t, Wt U.1 (cls (single U.2.carrier U.2.definable)) t) : RVSemiring M S →+* TensorProduct C R W := by
  let w (U : GradedObject M S) := (total U).choose
  let a (U : GradedObject M S) := cls (single U.2.carrier U.2.definable)
  have spec (U) : Wt U.1 (a U) (w U) := (total U).choose_spec
  apply descendWeights M S w
  intro p q rel
  have realized := congrArg (realizeScissors M S) (scissors_sound M S rel)
  cases rel with
  | iso U V iso =>
    have eq : a ⟨_,U⟩ = a ⟨_,V⟩ := (cls_eq_iff _ _).mpr (single_iso _ _ iso)
    simpa only [MvPolynomial.eval₂_X] using unique (spec ⟨_,U⟩) (eq.symm ▸ spec ⟨_,V⟩)
  | zero U h =>
    have eq : a ⟨_,U⟩ = 0 := (cls_eq_iff _ _).mpr (single_empty U.definable h)
    simpa only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_zero] using unique (spec ⟨_,U⟩) (eq.symm ▸ zero pull hv res val)
  | one U h =>
    have eq : a ⟨_,U⟩ = 1 := (cls_eq_iff _ _).mpr (single_unit U.definable h)
    simpa only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_one] using unique (spec ⟨_,U⟩) (eq.symm ▸ one pull hv res val)
  | cut U V T A B ha hb dj cv av bt =>
    have eq : a ⟨_,U⟩ = a ⟨_,V⟩ + a ⟨_,T⟩ := by
      change realizeScissors M S (objectClass M S ⟨_,U⟩) = realizeScissors M S (objectClass M S ⟨_,V⟩ + objectClass M S ⟨_,T⟩) at realized
      simpa only [map_add,realizeScissors_class] using realized
    simpa only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_add] using unique (spec ⟨_,U⟩)
      (eq.symm ▸ add pull hv res val (spec ⟨_,V⟩) (spec ⟨_,T⟩))
  | prod U V T iso =>
    have eq : a ⟨_,T⟩ = a ⟨_,U⟩ * a ⟨_,V⟩ := by
      change realizeScissors M S (objectClass M S ⟨_,T⟩) = realizeScissors M S (objectClass M S ⟨_,U⟩ * objectClass M S ⟨_,V⟩) at realized
      simpa only [map_mul,realizeScissors_class] using realized
    simpa only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_mul] using unique (spec ⟨_,T⟩)
      (eq.symm ▸ mul pull hv res val (spec ⟨_,U⟩) (spec ⟨_,V⟩))

theorem descend_object (unique : ∀ {k a x y}, Wt k a x → Wt k a y → x=y)
  (total : ∀ (U : GradedObject M S), ∃ t, Wt U.1 (cls (single U.2.carrier U.2.definable)) t)
    (U : RVObject M S k) {x} (h : Wt k (cls (single U.carrier U.definable)) x) :
    RectangleWeight.descend pull hv res val (@unique) total (objectClass M S ⟨k,U⟩) = x := by
  unfold descend
  rw [descendWeights_class]
  exact unique (total ⟨k,U⟩).choose_spec h

end RectangleWeight
end GeneralizedEuler.Section4
