module

public import Section4.SemiringGroupification
public import Section4.ResidueScissors
public import Section4.TaggedValueClasses
import all Section4.Factors
import all Section4.Scissors
import all Section4.ResidueScissors
import all Section4.TaggedValueClasses
import all Section4.DegreeZeroInclusion

/-! Lemma 4.22. An integer Euler characteristic gives a polynomial-valued
homomorphism by recording each object's ambient degree. The three maps
use the actual graded scissor presentations and extend to groupification. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2

namespace GradedEuler
variable {I H : Type*}

def mark (degree : I → ℕ) : MvPolynomial I ℕ →+* Polynomial (MvPolynomial I ℕ) :=
  MvPolynomial.eval₂Hom (Nat.castRingHom _) fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ degree i

@[simp] theorem mark_X (degree : I → ℕ) (i : I) :
    mark degree (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ degree i :=
  MvPolynomial.eval₂_X _ _ _

def InDegree (degree : I → ℕ) (p : MvPolynomial I ℕ) (n : ℕ) :=
  mark degree p = Polynomial.C p * Polynomial.X ^ n

theorem rename_mark (d : H → ℕ) (f : I → H) (p : MvPolynomial I ℕ) :
    Polynomial.map (MvPolynomial.rename (R := ℕ) f).toRingHom (mark (d ∘ f) p) =
    mark d (MvPolynomial.rename f p) := by
  let left := (Polynomial.mapRingHom (MvPolynomial.rename (R := ℕ) f).toRingHom).comp (mark (d ∘ f))
  let right := (mark d).comp (MvPolynomial.rename (R := ℕ) f).toRingHom
  have eq : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro n; exact DFunLike.congr_fun (Subsingleton.elim (left.comp MvPolynomial.C) (right.comp MvPolynomial.C)) n
    · intro i; simp [left,right,Function.comp_def]
  exact DFunLike.congr_fun eq p

theorem of_rename (d : H → ℕ) {f : I → H} (inj : Function.Injective f)
    {n} (p : MvPolynomial I ℕ) (h : InDegree d (MvPolynomial.rename f p) n) : InDegree (d ∘ f) p n := by
  apply Polynomial.map_injective (MvPolynomial.rename (R := ℕ) f).toRingHom (MvPolynomial.rename_injective f inj)
  rw [rename_mark]; simpa [InDegree] using h

variable {L : Language} {F : Type*} {Z : TCsort → Type*} (M : SortedStructure L F Z) (S : SortedSubstructure M)

theorem rv_homogeneous {p q} (h : RVRelation M S p q) :
    ∃ n, InDegree Sigma.fst p n ∧ InDegree Sigma.fst q n := by
  cases h with
  | iso U V _ => exact ⟨_,mark_X _ _,mark_X _ _⟩
  | zero U _ => exact ⟨_,mark_X _ _,by simp [InDegree]⟩
  | one U _ => exact ⟨0,mark_X _ _,by simp [InDegree]⟩
  | cut U V W _ _ _ _ _ _ _ _ => exact ⟨_,mark_X _ _,by simp [InDegree,add_mul]⟩
  | prod U V W _ => exact ⟨_,mark_X _ _,by simp [InDegree,pow_add]; ring⟩

theorem residue_homogeneous {Γ : Type*} (v : Z .rv → Γ) {p q} (h : residueRelation M S v p q) :
    ∃ n, InDegree (fun i : ResidueObject M S v => i.val.1) p n ∧
      InDegree (fun i : ResidueObject M S v => i.val.1) q n := by
  obtain ⟨n,hp,hq⟩ := rv_homogeneous M S h
  exact ⟨n,of_rename Sigma.fst Subtype.val_injective p hp,of_rename Sigma.fst Subtype.val_injective q hq⟩

variable {V : Type*} {J : Language} [J.Structure V] (A : Set V)

theorem value_homogeneous {p q} (h : ValueObject.Relation (J := J) A p q) :
    ∃ n, InDegree Sigma.fst p n ∧ InDegree Sigma.fst q n := by
  cases h with
  | iso U V _ => exact ⟨_,mark_X _ _,mark_X _ _⟩
  | empty U _ => exact ⟨_,mark_X _ _,by simp [InDegree]⟩
  | one U _ => exact ⟨0,mark_X _ _,by simp [InDegree]⟩
  | cut U V W _ => exact ⟨_,mark_X _ _,by simp [InDegree,add_mul]⟩
  | prod U V W _ => exact ⟨_,mark_X _ _,by simp [InDegree,pow_add]; ring⟩

variable (d : I → ℕ) (rel : MvPolynomial I ℕ → MvPolynomial I ℕ → Prop)
  (homogeneous : ∀ {p q}, rel p q → ∃ n, InDegree d p n ∧ InDegree d q n)
  {C : Type*} [CommSemiring C] (χ : (ringConGen rel).Quotient →+* C)

def polynomialMeasure : (ringConGen rel).Quotient →+* Polynomial C := by
  let ev := χ.comp (ringConGen rel).mk'
  let graded := (Polynomial.mapRingHom ev).comp (mark d)
  apply (ringConGen rel).lift graded
  apply RingCon.ringConGen_le.mpr
  intro p q h
  obtain ⟨n,hp,hq⟩ := homogeneous h
  have eq : ev p = ev q := congrArg χ (Quotient.sound (RingConGen.Rel.of p q h))
  change (mark d p).map ev = (mark d q).map ev
  rw [hp,hq]; simp [eq]

theorem polynomialMeasure_X (i : I) :
    polynomialMeasure d rel homogeneous χ ((ringConGen rel).mk' (MvPolynomial.X i)) =
      Polynomial.C (χ ((ringConGen rel).mk' (MvPolynomial.X i))) * Polynomial.X ^ d i := by
  change Polynomial.map (χ.comp (ringConGen rel).mk') (mark d (MvPolynomial.X i)) = _
  simp

def residue {Γ : Type*} (v : Z .rv → Γ) (euler : ResidueSemiring M S v →+* ℤ) :=
  SemiringGroupification.lift (polynomialMeasure _ _ (residue_homogeneous M S v) euler)

def value (euler : ValueObject.SemiringOfSets (J := J) A →+* ℤ) :=
  SemiringGroupification.lift (polynomialMeasure _ _ (value_homogeneous A) euler)

theorem residue_class {Γ : Type*} (v : Z .rv → Γ) (euler : ResidueSemiring M S v →+* ℤ)
    {k} (U : RVObject M S k) (hu : U.IsResidue M S v) :
    residue M S v euler (SemiringGroupification.of _ (residueClass U hu)) =
      Polynomial.C (euler (residueClass U hu)) * Polynomial.X ^ k := by
  rw [residue,SemiringGroupification.lift_of]
  exact polynomialMeasure_X _ _ (residue_homogeneous M S v) euler ⟨⟨k,U⟩,hu⟩

theorem value_class (euler : ValueObject.SemiringOfSets (J := J) A →+* ℤ)
    {k} (U : ValueObject.Over (J := J) A k) :
    value A euler (SemiringGroupification.of _ (taggedValueClass A U)) =
      Polynomial.C (euler (taggedValueClass A U)) * Polynomial.X ^ k := by
  rw [value,SemiringGroupification.lift_of]
  exact polynomialMeasure_X _ _ (value_homogeneous A) euler ⟨k,U⟩

end GradedEuler
end GeneralizedEuler.Section4
