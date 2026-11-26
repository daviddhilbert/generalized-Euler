module

public import Section4.RectangleRange
public import Section4.SignedValueGeneration
import all Section4.RectangleMap
import all Section4.Factors
import all Section4.ResidueScissors
import all Section4.ValueScissors
import all Section4.DegreeZeroInclusion
import all Section4.Scissors

/-! Agreement on actual homogeneous generators suffices to recover both
factors, and then every element of the balanced tensor product. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct

theorem presented_hom_ext {I T : Type*} [CommSemiring T] (rel : MvPolynomial I ℕ → MvPolynomial I ℕ → Prop)
    (f g : (ringConGen rel).Quotient →+* T) (h : ∀ i, f ((ringConGen rel).mk' (MvPolynomial.X i)) = g ((ringConGen rel).mk' (MvPolynomial.X i))) :
    f=g := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := (ringConGen rel).mk'_surjective x
  induction p using MvPolynomial.induction_on with
  | C n => rw [show MvPolynomial.C n = (n : MvPolynomial I ℕ) from map_natCast _ n]; simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,hp,h]

theorem includeResidue_class {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
    {Γ : Type*} {v : Z .rv → Γ} {n} (U : RVObject M S n) (hu : U.IsResidue M S v) :
    includeResidue M S v (residueClass U hu) = objectClass M S ⟨n,U⟩ := by
  change (ringConGen (RVRelation M S)).mk' (MvPolynomial.rename Subtype.val
    (MvPolynomial.X (⟨_,hu⟩ : ResidueObject M S v))) = _
  rw [MvPolynomial.rename_X]; rfl

theorem recover_signed_pieces {V : Type*} {Z : Type} [Fintype Z] {J H : Language} [J.Structure V] [H.Structure (Z × V)]
    {T : Type*} [CommSemiring T] (G : Set V) (A : Set (Z × V)) (one : Z)
    (interpret : SignedInterpretation (J := J) (H := H) G A)
    (f g : SemiringOfSets (J := H) A →+* T)
    (pos : ∀ {n} (D : Set (Fin n → V)) (hd : G.Definable J D),
      let a := pieceClass (signInsert (fun _ => one) '' D) (signed_stratum_definable G A @interpret _ _ hd)
      f a = g a) : f=g := by
  apply presented_hom_ext _ f g
  rintro ⟨k,U⟩
  change f (taggedValueClass A U) = g (taggedValueClass A U)
  rw [taggedValueClass_eq_sum, map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [signed_piece_decomposition G A one @interpret _ (U.isDefinable i),map_sum,map_sum]
  exact Finset.sum_congr rfl fun b _ => pos _ ((interpret _).mp (U.isDefinable i) b)

theorem tensor_left_inverse_of_factors {C R W T : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
    [CommSemiring T] [Algebra C R] [Algebra C W] (F : R ⊗[C] W →+* T) (B : T →+* R ⊗[C] W)
    (r : R →+* T) (w : W →+* T) (forward : ∀ x y, F (x ⊗ₜ[C] y) = r x * w y)
    (left : B.comp r = (Algebra.TensorProduct.includeLeft : R →ₐ[C] R ⊗[C] W).toRingHom)
    (right : B.comp w = (Algebra.TensorProduct.includeRight : W →ₐ[C] R ⊗[C] W).toRingHom) :
    Function.LeftInverse B F := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [forward,map_mul]
    have h₁ : B (r a) = a ⊗ₜ[C] (1 : W) := DFunLike.congr_fun left a
    have h₂ : B (w b) = (1 : R) ⊗ₜ[C] b := DFunLike.congr_fun right b
    simp only [h₁,h₂,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | add x y hx hy => simp only [map_add,hx,hy]

end GeneralizedEuler.Section4
