module

public import Section4.PositiveResidueLineCut
public import Section4.HomogeneousValueLift
import all Section4.HomogeneousValueLift
import all Section4.RVLineCut
import all Section4.FiniteFiberEuler

/-! The degree-one value lift has no additive left inverse. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
  (hO : IsOrderConvex O) {J H : Language} [J.Structure K] [J.Structure (Residue O)]
  [H.Structure (SignedValueGroup O)] (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
local notation "M" => canonicalStructure (L := J) O hO P
local notation "val" => signedLabel O hO
variable (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable H D → isRVSet (canonicalStructure (L := J) O hO P) S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (liftIso : ∀ {k} (D E : Set (Fin k → SignedValueGroup O)), A.Definable H D → A.Definable H E →
    ∀ f : D ≃ E, A.Definable H {z : Fin k ⊕ Fin k → SignedValueGroup O | ∃ x : D, x.val = z ∘ Sum.inl ∧ (f x).val = z ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D) (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) E))

theorem no_additive_value_retraction (terms : OrderedFieldTerms J)
    (h : InterpretsFieldTerms (K := Residue O) terms.toFieldTerms)
    (one : terms.one.realize (Empty.elim : Empty → Residue O) = 1)
    (he : A.Definable H ({1} : Set (Fin 1 → SignedValueGroup O))) :
    ¬ ∃ r : homogeneousRV M S 1 →+ homogeneousValue (J := H) A 1,
      Function.LeftInverse r (homogeneousValueLift A M S val defSharp liftIso 1) := by
  rintro ⟨r,left⟩
  let e := homogeneousPiece A _ he
  let U := sharpObject M S val _ (defSharp he)
  have lift := homogeneousValueLift_piece A M S val defSharp liftIso _ he
  have sends : r (homogeneousRVClass U) = e := lift ▸ left e
  obtain ⟨R,cut⟩ := positive_residue_line_cut O hO P S terms h one (defSharp he)
  let back := (homogeneousValue (J := H) A 1).subtype.comp r
  apply no_additive_splitting_of_line_cut A (1 : Fin 1 → SignedValueGroup O) he
    (homogeneousRVClass U) (homogeneousRVClass R) cut back back.map_add
  exact congrArg Subtype.val sends

end GeneralizedEuler.Section4
