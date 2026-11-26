module

public import Section4.RectangleMap
import all Section4.RectangleMap
import all Section4.Factors
import all Section4.ResidueScissors
import all Section4.Scissors

/-! Pure tensors and generation of the range of the concrete rectangle map. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject MvPolynomial
open scoped TensorProduct

theorem rectangleHom_pure {R V T : Type*} [CommSemiring R] [CommSemiring V] [CommSemiring T]
    (r : R →+* T) (v : V →+* T) (t : R) (e : V) (balance : r t = v e) (a : R) (b : V) :
    letI := (Polynomial.eval₂RingHom (Nat.castRingHom R) t).toAlgebra
    letI := (Polynomial.eval₂RingHom (Nat.castRingHom V) e).toAlgebra
    rectangleHom r v t e balance (a ⊗ₜ[Polynomial ℕ] b) = r a * v b := by
  rfl

theorem generators_in_range {L : Language} {E : Type*} {Z : TCsort → Type*}
    {M : SortedStructure L E Z} {S : SortedSubstructure M}
    {T : Type*} [CommSemiring T] (f : T →+* RVSemiring M S)
    (classes : ∀ U, objectClass M S U ∈ f.rangeS) : Function.Surjective f := by
  intro a
  obtain ⟨p,rfl⟩ := (ringConGen (RVRelation M S)).mk'_surjective a
  change (ringConGen (RVRelation M S)).mk' p ∈ f.rangeS
  induction p using MvPolynomial.induction_on with
  | C n =>
    rw [show C n = (n : RVExpression M S) from map_natCast _ n,map_natCast]
    exact ⟨(n : T),map_natCast f n⟩
  | add p q hp hq => rw [map_add]; exact f.rangeS.add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact f.rangeS.mul_mem hp (classes i)

variable {L J : Language} {E : Type*} {Z : TCsort → Type*} {Γ : Type*} [J.Structure Γ]
  (M : SortedStructure L E Z) (S : SortedSubstructure M) (v : Z .rv → Γ) (A : Set Γ)
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  (liftIso : ∀ {k} (D B : Set (Fin k → Γ)), A.Definable J D → A.Definable J B →
    ∀ e : D ≃ B, A.Definable J {w : Fin k ⊕ Fin k → Γ |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent M S.carrier (sharp M v D) (sharp M v B))
  (e : Fin 1 → Γ) (he : A.Definable J ({e} : Set (Fin 1 → Γ)))

theorem product_in_rectangle_range {k l} (U : RVObject M S k) (hu : U.IsResidue M S v)
    (D : Set (Fin l → Γ)) (hd : A.Definable J D) :
    objectClass M S ⟨k,U⟩ * objectClass M S ⟨l,sharpObject M S v D (defSharp hd)⟩ ∈
      (balancedRectangleMap M S v A defSharp liftIso e he).rangeS := by
  let t := residueClass (sharpObject M S v {e} (defSharp he))
    (sharp_residue M S v A defSharp {e} (Set.finite_singleton _) he)
  let := (Polynomial.eval₂RingHom (Nat.castRingHom _) t).toAlgebra
  let := (Polynomial.eval₂RingHom (Nat.castRingHom _) (pieceClass {e} he)).toAlgebra
  refine ⟨residueClass U hu ⊗ₜ[Polynomial ℕ] pieceClass D hd,?_⟩
  have eq := rectangleHom_pure (includeResidue M S v) (valueFactorHom M S v A defSharp liftIso)
    t (pieceClass {e} he) (balance_finite_value M S v A defSharp liftIso {e} (Set.finite_singleton _) he)
    (residueClass U hu) (pieceClass D hd)
  rw [valueFactorHom_piece] at eq
  apply eq.trans
  apply congrArg (· * _)
  change (ringConGen (RVRelation M S)).mk' (rename Subtype.val
    (X (⟨⟨k,U⟩,hu⟩ : ResidueObject M S v))) = _
  rw [rename_X]; rfl

end GeneralizedEuler.Section4
