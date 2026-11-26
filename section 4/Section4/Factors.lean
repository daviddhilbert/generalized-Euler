module

public import Section4.Scissors
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.TensorProduct.Maps

/-! The residue and value factor semirings. Restriction to RES takes place
on the generating object relations, before the congruence is formed. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 MvPolynomial
open scoped TensorProduct
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
  (M : SortedStructure L E Z) (S : SortedSubstructure M)
  {Γ : Type*} (vrv : Z .rv → Γ)

abbrev ResidueObject := {p : GradedObject M S // p.2.IsResidue M S vrv}

def residueRelation (a b : MvPolynomial (ResidueObject M S vrv) ℕ) : Prop :=
  RVRelation M S (rename Subtype.val a) (rename Subtype.val b)

abbrev ResidueSemiring := (ringConGen (residueRelation M S vrv)).Quotient

/-- Forgetting the finite-value condition respects each individual RES
relation and induces the natural homomorphism into RV. -/
def includeResidue : ResidueSemiring M S vrv →+* RVSemiring M S := by
  let f := ((ringConGen (RVRelation M S)).mk').comp
    (rename (R := ℕ) (Subtype.val : ResidueObject M S vrv → GradedObject M S)).toRingHom
  exact (ringConGen _).lift f (RingCon.ringConGen_le.mpr fun _ _ h => scissors_sound M S h)

namespace ValueObject
variable {Γ : Type*} {J : Language} [J.Structure Γ] (A : Set Γ)
abbrev Over := ValueObject (fun _ D => A.Definable J D)

def points {k} (U : Over (J := J) A k) := Σ t, U.piece t

/-- Definability of a map between tagged unions is tested on each fixed
pair of tags. -/
def Isomorphic {k l} (U : Over (J := J) A k) (V : Over (J := J) A l) : Prop :=
  ∃ e : U.points A ≃ V.points A, ∀ i j, A.Definable J {v : Fin k ⊕ Fin l → Γ |
    ∃ x : U.piece i, x.val = v ∘ Sum.inl ∧ ∃ y : V.piece j,
      y.val = v ∘ Sum.inr ∧ e ⟨i,x⟩ = ⟨j,y⟩}

def IsCut {k} (U V W : Over (J := J) A k) : Prop :=
  ∃ e : U.points A ≃ (V.points A ⊕ W.points A),
    (∀ i j, A.Definable J {v : Fin k ⊕ Fin k → Γ | ∃ x : U.piece i,
      x.val = v ∘ Sum.inl ∧ ∃ y : V.piece j, y.val = v ∘ Sum.inr ∧ e ⟨i,x⟩ = .inl ⟨j,y⟩}) ∧
    (∀ i j, A.Definable J {v : Fin k ⊕ Fin k → Γ | ∃ x : U.piece i,
      x.val = v ∘ Sum.inl ∧ ∃ y : W.piece j, y.val = v ∘ Sum.inr ∧ e ⟨i,x⟩ = .inr ⟨j,y⟩})

def IsProduct {k l} (U : Over (J := J) A k) (V : Over (J := J) A l)
    (W : Over (J := J) A (k+l)) : Prop :=
  ∃ e : (U.points A × V.points A) ≃ W.points A, ∀ i j t,
    A.Definable J {v : (Fin k ⊕ Fin l) ⊕ Fin (k+l) → Γ | ∃ x : U.piece i, ∃ y : V.piece j,
      x.val = v ∘ Sum.inl ∘ Sum.inl ∧ y.val = v ∘ Sum.inl ∘ Sum.inr ∧
      ∃ z : W.piece t, z.val = v ∘ Sum.inr ∧ e (⟨i,x⟩,⟨j,y⟩) = ⟨t,z⟩}

abbrev Graded := Σ k, Over (J := J) A k

inductive Relation : MvPolynomial (Graded (J := J) A) ℕ → MvPolynomial (Graded (J := J) A) ℕ → Prop where
  | iso {k} (U V : Over (J := J) A k) (h : U.Isomorphic A V) :
      Relation (X ⟨k,U⟩) (X ⟨k,V⟩)
  | empty {k} (U : Over (J := J) A k) (h : IsEmpty (U.points A)) : Relation (X ⟨k,U⟩) 0
  | one (U : Over (J := J) A 0) (h : Nonempty (Unique (U.points A))) : Relation (X ⟨0,U⟩) 1
  | cut {k} (U V W : Over (J := J) A k) (h : U.IsCut A V W) :
      Relation (X ⟨k,U⟩) (X ⟨k,V⟩ + X ⟨k,W⟩)
  | prod {k l} (U : Over (J := J) A k) (V : Over (J := J) A l) (W : Over (J := J) A (k+l))
      (h : U.IsProduct A V W) : Relation (X ⟨k+l,W⟩) (X ⟨k,U⟩ * X ⟨l,V⟩)

abbrev SemiringOfSets := (ringConGen (Relation (J := J) A)).Quotient
end ValueObject

section TensorMap
variable {R V T : Type*} [CommSemiring R] [CommSemiring V] [CommSemiring T]

/-- Balancing over all finite value classes follows from agreement on the
degree-one point. The constant coefficients are natural cardinalities. -/
def rectangleHom (r : R →+* T) (v : V →+* T) (t : R) (e : V) (balance : r t = v e) :
    letI := (Polynomial.eval₂RingHom (Nat.castRingHom R) t).toAlgebra
    letI := (Polynomial.eval₂RingHom (Nat.castRingHom V) e).toAlgebra
    R ⊗[Polynomial ℕ] V →+* T := by
  let r0 := Polynomial.eval₂RingHom (Nat.castRingHom R) t
  let v0 := Polynomial.eval₂RingHom (Nat.castRingHom V) e
  letI := r0.toAlgebra
  letI := v0.toAlgebra
  letI := (r.comp r0).toAlgebra
  have same : v.comp v0 = r.comp r0 := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [v0,r0,balance]
  letI : IsScalarTower (Polynomial ℕ) (Polynomial ℕ) R :=
    ⟨fun a b x => by change r0 (a*b) * x = r0 a * (r0 b * x); rw [map_mul,mul_assoc]⟩
  letI : IsScalarTower (Polynomial ℕ) (Polynomial ℕ) T :=
    ⟨fun a b x => by change (r.comp r0) (a*b) * x = (r.comp r0) a * ((r.comp r0) b * x); rw [map_mul,mul_assoc]⟩
  let a : R →ₐ[Polynomial ℕ] T := { r with commutes' := fun _ => rfl }
  let b : V →ₐ[Polynomial ℕ] T := { v with commutes' := fun x => DFunLike.congr_fun same x }
  exact (Algebra.TensorProduct.lift (R := Polynomial ℕ) (S := Polynomial ℕ) a b (fun _ _ => Commute.all ..)).toRingHom

end TensorMap
end GeneralizedEuler.Section4
