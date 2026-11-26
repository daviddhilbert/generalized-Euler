module

public import Section4.Scissors
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! The Grothendieck ring of a commutative semiring by its universal
property. Every semiring map to a ring extends uniquely. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
namespace SemiringGroupification
open MvPolynomial
variable (R : Type*) [CommSemiring R]

inductive Relation : MvPolynomial R ℤ → MvPolynomial R ℤ → Prop where
  | zero : Relation (X 0) 0
  | one : Relation (X 1) 1
  | add (a b : R) : Relation (X (a+b)) (X a + X b)
  | mul (a b : R) : Relation (X (a*b)) (X a * X b)

abbrev Ring := (ringConGen (Relation R)).Quotient

def of : R →+* Ring R where
  toFun x := (ringConGen (Relation R)).mk' (X x)
  map_zero' := Quotient.sound (RingConGen.Rel.of _ _ (.zero : Relation R _ _))
  map_one' := Quotient.sound (RingConGen.Rel.of _ _ (.one : Relation R _ _))
  map_add' a b := Quotient.sound (RingConGen.Rel.of _ _ (.add a b : Relation R _ _))
  map_mul' a b := Quotient.sound (RingConGen.Rel.of _ _ (.mul a b : Relation R _ _))

variable {R} {T : Type*} [CommRing T]

def lift (f : R →+* T) : Ring R →+* T :=
  (ringConGen (Relation R)).lift (eval₂Hom (Int.castRingHom T) f)
    (RingCon.ringConGen_le.mpr (by intro a b h; cases h <;> simp))

@[simp] theorem lift_of (f : R →+* T) (a : R) : lift f (of R a) = f a :=
  eval₂_X _ _ _

theorem hom_ext {f g : Ring R →+* T} (agree : ∀ a, f (of R a) = g (of R a)) : f=g := by
  let q := (ringConGen (Relation R)).mk'
  have h : f.comp q = g.comp q := by
    apply MvPolynomial.ringHom_ext
    · intro z
      exact DFunLike.congr_fun (Subsingleton.elim ((f.comp q).comp C) ((g.comp q).comp C)) z
    · exact agree
  apply RingHom.ext; intro x
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  exact DFunLike.congr_fun h a

def universal : (R →+* T) ≃ (Ring R →+* T) where
  toFun := lift
  invFun f := f.comp (of R)
  left_inv f := RingHom.ext fun x => lift_of f x
  right_inv f := hom_ext fun a => lift_of (f.comp (of R)) a

def map {V : Type*} [CommSemiring V] (f : R →+* V) : Ring R →+* Ring V := lift ((of V).comp f)

@[simp] theorem map_of {V : Type*} [CommSemiring V] (f : R →+* V) (x : R) :
    map f (of R x) = of V (f x) := lift_of _ _

end SemiringGroupification
end GeneralizedEuler.Section4
