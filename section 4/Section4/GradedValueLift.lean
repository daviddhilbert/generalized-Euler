module

public import Section4.GradedEulerMaps
public import Section4.HomogeneousValueLift
import all Section4.GradedEulerMaps
import all Section4.HomogeneousValueLift
import all Section4.ValueFactorMap
import all Section4.ValueScissors
import all Section4.Factors
import all Section4.Scissors

/-! Degreewise injectivity implies injectivity on the whole value
semiring. Coefficient projections also restrict any additive splitting
of the full semiring to a splitting in each homogeneous degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open FirstOrder GeneralizedEuler.Section2 ValueObject GradedEuler
variable {Γ : Type*} {J : Language} [J.Structure Γ] (A : Set Γ)

theorem value_piece_induction (P : SemiringOfSets (J := J) A → Prop)
    (zero : P 0) (add : ∀ x y, P x → P y → P (x+y))
    (piece : ∀ {k} (D : Set (Fin k → Γ)) (hd : A.Definable J D), P (pieceClass D hd)) (x) : P x := by
  let S : Set (SemiringOfSets (J := J) A) := {x | ∃ (k : ℕ) (D : Set (Fin k → Γ)) (hd : A.Definable J D), pieceClass D hd = x}
  let T := AddSubmonoid.closure S
  have mem {k} (D : Set (Fin k → Γ)) (hd : A.Definable J D) : pieceClass D hd ∈ T :=
    AddSubmonoid.subset_closure ⟨k,D,hd,rfl⟩
  have mul {x y} (hx : x∈T) (hy : y∈T) : x*y∈T := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨_,D,hd,rfl⟩ := hx
      induction hy using AddSubmonoid.closure_induction with
      | mem y hy => obtain ⟨_,E,he,rfl⟩ := hy; rw [← pieceClass_product hd he]; exact mem _ _
      | zero => rw [mul_zero]; exact T.zero_mem
      | add a b _ _ ha hb => rw [mul_add]; exact T.add_mem ha hb
    | zero => rw [zero_mul]; exact T.zero_mem
    | add a b _ _ ha hb => rw [add_mul]; exact T.add_mem ha hb
  have one : (1 : SemiringOfSets (J := J) A) ∈ T := by
    let z : Fin 0 → Γ := Fin.elim0
    have eq : ({z} : Set (Fin 0 → Γ)) = Set.univ := Set.eq_univ_of_forall (fun _ => Subsingleton.elim _ _)
    have hd : A.Definable J {z} := eq ▸ Set.definable_univ
    rw [← pieceClass_degree_zero z hd]; exact mem _ _
  have all : x∈T := by
    obtain ⟨p,rfl⟩ := (ringConGen (ValueObject.Relation (J := J) A)).mk'_surjective x
    induction p using MvPolynomial.induction_on with
    | C n =>
      rw [show MvPolynomial.C n = (n : MvPolynomial _ ℕ) from map_natCast _ n,map_natCast,← nsmul_one]
      exact T.nsmul_mem one n
    | add p q hp hq => rw [map_add]; exact T.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]; apply mul hp
      change taggedValueClass A i.2 ∈ T
      rw [taggedValueClass_eq_sum]; exact T.sum_mem fun _ _ => mem _ _
  have gen (v) (hv : v∈S) : P v := by
    obtain ⟨_,D,hd,eq⟩ := hv
    exact eq ▸ piece D hd
  exact AddSubmonoid.closure_induction (s := S) (motive := fun x _ => P x)
    gen zero (fun a b _ _ => add a b) all

def valueDegreePolynomial := polynomialMeasure Sigma.fst (ValueObject.Relation (J := J) A)
  (value_homogeneous A) (RingHom.id _)

theorem valueDegree_piece {k} (D : Set (Fin k → Γ)) (hd : A.Definable J D) :
    valueDegreePolynomial A (pieceClass D hd) = Polynomial.C (pieceClass D hd) * Polynomial.X^k :=
  polynomialMeasure_X Sigma.fst (ValueObject.Relation (J := J) A) (value_homogeneous A) (RingHom.id _) ⟨k,single D hd⟩

theorem valueDegree_coeff (x : SemiringOfSets (J := J) A) (k : ℕ) :
    (valueDegreePolynomial A x).coeff k ∈ homogeneousValue A k := by
  induction x using value_piece_induction A with
  | zero => simp
  | add x y hx hy => simpa only [map_add,Polynomial.coeff_add] using (homogeneousValue A k).add_mem hx hy
  | piece D hd =>
    rw [valueDegree_piece,Polynomial.coeff_C_mul_X_pow]
    split
    · next h => subst k; exact (homogeneousPiece A D hd).property
    · exact (homogeneousValue A k).zero_mem

theorem valueDegree_eval (x : SemiringOfSets (J := J) A) : (valueDegreePolynomial A x).eval 1=x := by
  induction x using value_piece_induction A with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | piece D hd => rw [valueDegree_piece]; simp

theorem homogeneous_degree_fixed {k} (x : homogeneousValue (J := J) A k) :
    (valueDegreePolynomial A x.val).coeff k = x.val := by
  obtain ⟨x,hx⟩ := x
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => obtain ⟨D,hd,rfl⟩ := hx; simp [valueDegree_piece]
  | zero => simp
  | add a b _ _ ha hb => simp_all

def valueDegreeProjection (k : ℕ) : SemiringOfSets (J := J) A →+ homogeneousValue (J := J) A k :=
  ((Polynomial.lcoeff _ k).toAddMonoidHom.comp (valueDegreePolynomial A).toAddMonoidHom).codRestrict _ (fun x => valueDegree_coeff A x k)

variable {F : Type*} {L : Language} {Z : TCsort → Type*}
  (M : SortedStructure L F Z) (S : SortedSubstructure M) (v : Z .rv → Γ)
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  (liftIso : ∀ {k} (D E : Set (Fin k → Γ)), A.Definable J D → A.Definable J E →
    ∀ f : D ≃ E, A.Definable J {z : Fin k ⊕ Fin k → Γ | ∃ x : D, x.val = z ∘ Sum.inl ∧ (f x).val = z ∘ Sum.inr} →
      RVDefinablyEquivalent M S.carrier (sharp M v D) (sharp M v E))
local notation "liftV" => valueFactorHom M S v A defSharp liftIso
local notation "liftK" => homogeneousValueLift A M S v defSharp liftIso
local notation "rvMark" => polynomialMeasure Sigma.fst (RVRelation M S) (rv_homogeneous M S) (RingHom.id _)

theorem valueDegree_natural (x : SemiringOfSets (J := J) A) :
    (valueDegreePolynomial A x).map liftV = rvMark (liftV x) := by
  induction x using value_piece_induction A with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | piece D hd =>
    rw [valueDegree_piece,valueFactorHom_piece]
    rw [show rvMark (objectClass M S ⟨_,sharpObject M S v D (defSharp hd)⟩) = _ from
      polynomialMeasure_X Sigma.fst (RVRelation M S) (rv_homogeneous M S) (RingHom.id _) ⟨_,sharpObject M S v D (defSharp hd)⟩]
    simp [valueFactorHom_piece,objectClass]

theorem graded_value_injective (degree : ∀ k, Function.Injective (liftK k)) : Function.Injective liftV := by
  intro x y heq
  have marked := (valueDegree_natural A M S v defSharp liftIso x).trans
    ((congrArg rvMark heq).trans (valueDegree_natural A M S v defSharp liftIso y).symm)
  have same : valueDegreePolynomial A x=valueDegreePolynomial A y := by
    ext k
    have h := congrArg (fun p => Polynomial.coeff p k) marked
    simp only [Polynomial.coeff_map] at h
    exact congrArg Subtype.val (degree k (a₁ := valueDegreeProjection A k x) (a₂ := valueDegreeProjection A k y) (Subtype.ext h))
  exact (valueDegree_eval A x).symm.trans ((congrArg (Polynomial.eval 1) same).trans (valueDegree_eval A y))

theorem full_retraction_restricts (f : RVSemiring M S →+ SemiringOfSets (J := J) A) (left : Function.LeftInverse f liftV) (k : ℕ) :
    ∃ r : homogeneousRV M S k →+ homogeneousValue (J := J) A k, Function.LeftInverse r (liftK k) :=
  ⟨(valueDegreeProjection A k).comp (f.comp (homogeneousRV M S k).subtype),fun x => Subtype.ext (by
    change (valueDegreePolynomial A (f (liftV x.val))).coeff k = x.val
    rw [left,homogeneous_degree_fixed])⟩

end GeneralizedEuler.Section4
