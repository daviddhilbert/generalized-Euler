module

public import Section4.ValueFactorMap
public import Section4.ResidueScissors
import all Section4.ResidueScissors
import all Section4.Factors
import all Section4.ValuePullback
import all Section4.Objects

/-! The balanced map of the manuscript for the presented residue and value categories. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
variable {L J : Language} {E : Type*} {Z : TCsort → Type*} {Γ : Type*} [J.Structure Γ]
  (M : SortedStructure L E Z) (S : SortedSubstructure M) (v : Z .rv → Γ) (A : Set Γ)
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  (liftIso : ∀ {k} (D B : Set (Fin k → Γ)), A.Definable J D → A.Definable J B →
    ∀ e : D ≃ B, A.Definable J {w : Fin k ⊕ Fin k → Γ |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent M S.carrier (sharp M v D) (sharp M v B))

theorem sharp_residue {k} (D : Set (Fin k → Γ)) (fin : D.Finite) (hd : A.Definable J D) :
    (sharpObject M S v D (defSharp hd)).IsResidue M S v := by
  apply fin.subset
  rintro _ ⟨x,rfl⟩
  exact x.property.2

theorem balance_finite_value {k} (D : Set (Fin k → Γ)) (fin : D.Finite) (hd : A.Definable J D) :
    includeResidue M S v (residueClass (sharpObject M S v D (defSharp hd)) (sharp_residue M S v A defSharp D fin hd)) =
      valueFactorHom M S v A defSharp liftIso (pieceClass D hd) := by
  rw [valueFactorHom_piece]
  change (ringConGen (RVRelation M S)).mk' (MvPolynomial.rename Subtype.val
    (MvPolynomial.X (⟨_,sharp_residue M S v A defSharp D fin hd⟩ : ResidueObject M S v))) = _
  rw [MvPolynomial.rename_X]
  rfl

def balancedRectangleMap (e : Fin 1 → Γ) (he : A.Definable J ({e} : Set (Fin 1 → Γ))) :
    let t := residueClass (sharpObject M S v {e} (defSharp he))
      (sharp_residue M S v A defSharp {e} (Set.finite_singleton _) he)
    letI := (Polynomial.eval₂RingHom (Nat.castRingHom _) t).toAlgebra
    letI := (Polynomial.eval₂RingHom (Nat.castRingHom _) (pieceClass {e} he)).toAlgebra
    ResidueSemiring M S v ⊗[Polynomial ℕ] SemiringOfSets (J := J) A →+* RVSemiring M S :=
  rectangleHom (includeResidue M S v) (valueFactorHom M S v A defSharp liftIso) _ _
    (balance_finite_value M S v A defSharp liftIso {e} (Set.finite_singleton _) he)

end GeneralizedEuler.Section4
