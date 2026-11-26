module

public import Section4.TaggedValueClasses
public import Section4.RVLineCut
import all Section4.RVLineCut
import all Section4.ValueScissors
import all Section4.ValuePullback
import all Section4.Factors

/-! Degreewise value semigroups and the restriction of the natural
value-factor map to the given ambient degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
variable {L J : Language} {F Γ : Type*} [J.Structure Γ] (A : Set Γ)

def homogeneousValue (k : ℕ) : AddSubmonoid (SemiringOfSets (J := J) A) :=
  AddSubmonoid.closure {c | ∃ (D : Set (Fin k → Γ)) (hd : A.Definable J D), pieceClass D hd = c}

def homogeneousPiece {k} (D : Set (Fin k → Γ)) (hd : A.Definable J D) : homogeneousValue (J := J) A k :=
  ⟨pieceClass D hd,AddSubmonoid.subset_closure ⟨_,_,rfl⟩⟩

theorem taggedValueClass_mem {k} (U : Over (J := J) A k) : taggedValueClass A U ∈ homogeneousValue A k := by
  rw [taggedValueClass_eq_sum]
  exact (homogeneousValue A k).sum_mem fun i _ => (homogeneousPiece A (U.piece i) (U.isDefinable i)).property

variable {Z : TCsort → Type*} (M : SortedStructure L F Z) (S : SortedSubstructure M) (v : Z .rv → Γ)
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  (liftIso : ∀ {k} (D E : Set (Fin k → Γ)), A.Definable J D → A.Definable J E →
    ∀ f : D ≃ E, A.Definable J {z : Fin k ⊕ Fin k → Γ | ∃ x : D, x.val = z ∘ Sum.inl ∧ (f x).val = z ∘ Sum.inr} →
      RVDefinablyEquivalent M S.carrier (sharp M v D) (sharp M v E))
local notation "mapV" => valueFactorHom M S v A defSharp liftIso

def homogeneousValueLift (k : ℕ) : homogeneousValue (J := J) A k →+ homogeneousRV M S k :=
  let f := (mapV).toAddMonoidHom.comp (homogeneousValue (J := J) A k).subtype
  f.codRestrict _ (fun x => by
    have sub : homogeneousValue (J := J) A k ≤ (homogeneousRV M S k).comap (mapV).toAddMonoidHom := by
      apply AddSubmonoid.closure_le.mpr
      rintro _ ⟨D,hd,rfl⟩
      change mapV (pieceClass D hd) ∈ homogeneousRV M S k
      rw [valueFactorHom_piece]
      exact (homogeneousRVClass _).property
    exact sub x.property)

theorem homogeneousValueLift_piece {k} (D : Set (Fin k → Γ)) (hd : A.Definable J D) :
    homogeneousValueLift A M S v defSharp liftIso k (homogeneousPiece A D hd) =
      homogeneousRVClass (sharpObject M S v D (defSharp hd)) :=
  Subtype.ext (valueFactorHom_piece M S v A defSharp liftIso D hd)

end GeneralizedEuler.Section4
