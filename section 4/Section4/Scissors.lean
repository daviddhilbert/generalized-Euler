module

public import Section4.Objects
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Congruence.Hom

/-! A presentation by actual fixed-base definable bijections and finite cuts.
The degree is carried by each generator independently of its tuple arity. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
variable (M : SortedStructure L E Z) (S : SortedSubstructure M)

abbrev GradedObject := Σ k, RVObject M S k
abbrev RVExpression := MvPolynomial (GradedObject M S) ℕ

def productSet {I J T : Type*} (U : Set (I → T)) (V : Set (J → T)) :
    Set (I ⊕ J → T) := {x | x ∘ Sum.inl ∈ U ∧ x ∘ Sum.inr ∈ V}

/-- In a cut, each part has the degree of the whole object. The component
bijections allow different underlying arities and arbitrary structure maps. -/
inductive RVRelation : RVExpression M S → RVExpression M S → Prop where
  | iso {k} (U V : RVObject M S k) (e : U.Isomorphic M S V) :
      RVRelation (MvPolynomial.X ⟨k,U⟩) (MvPolynomial.X ⟨k,V⟩)
  | zero {k} (U : RVObject M S k) (h : U.carrier = ∅) :
      RVRelation (MvPolynomial.X ⟨k,U⟩) 0
  | one (U : RVObject M S 0) (h : ∃ x, U.carrier = {x}) :
      RVRelation (MvPolynomial.X ⟨0,U⟩) 1
  | cut {k} (U V W : RVObject M S k) (A B : Set (Fin U.arity → Z .rv))
      (ha : isRVSet M S A) (hb : isRVSet M S B) (disj : Disjoint A B) (cover : A ∪ B = U.carrier)
      (ea : RVDefinablyEquivalent M S.carrier A V.carrier)
      (eb : RVDefinablyEquivalent M S.carrier B W.carrier) :
      RVRelation (MvPolynomial.X ⟨k,U⟩) (MvPolynomial.X ⟨k,V⟩ + MvPolynomial.X ⟨k,W⟩)
  | prod {k l} (U : RVObject M S k) (V : RVObject M S l) (W : RVObject M S (k+l))
      (e : RVDefinablyEquivalent M S.carrier (productSet U.carrier V.carrier) W.carrier) :
      RVRelation (MvPolynomial.X ⟨k+l,W⟩) (MvPolynomial.X ⟨k,U⟩ * MvPolynomial.X ⟨l,V⟩)

abbrev RVSemiring := (ringConGen (RVRelation M S)).Quotient

@[expose] def objectClass (U : GradedObject M S) : RVSemiring M S :=
  (ringConGen (RVRelation M S)).mk' (MvPolynomial.X U)

theorem scissors_sound {a b} (h : RVRelation M S a b) :
    (ringConGen (RVRelation M S)).mk' a = (ringConGen (RVRelation M S)).mk' b :=
  Quotient.sound (RingConGen.Rel.of _ _ h)

/-- Extend chart weights to the whole semiring after checking the object
relations. This construction works before groupification. -/
@[expose] def descendWeights {T : Type*} [CommSemiring T] (w : GradedObject M S → T)
    (h : ∀ a b, RVRelation M S a b →
      MvPolynomial.eval₂ (Nat.castRingHom T) w a = MvPolynomial.eval₂ (Nat.castRingHom T) w b) :
    RVSemiring M S →+* T :=
  (ringConGen (RVRelation M S)).lift (MvPolynomial.eval₂Hom (Nat.castRingHom T) w)
    (RingCon.ringConGen_le.mpr h)

@[simp] theorem descendWeights_class {T : Type*} [CommSemiring T] (w : GradedObject M S → T)
    (h) (U : GradedObject M S) : descendWeights M S w h (objectClass M S U) = w U :=
  MvPolynomial.eval₂_X _ _ _

end GeneralizedEuler.Section4
