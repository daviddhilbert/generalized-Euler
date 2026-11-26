module

public import Section4.ValuePadding
public import Section4.ValueEmbedding
public import Section4.ResidueProducts
import all Section4.SignedRectangleFactors
import all Section4.RectangleMap
import all Section4.ValueDescent
import all Section4.ValueEmbedding
import all Section4.ValuePadding
import all Section4.ResidueWeights
import all Section4.ResidueProducts
import all Section4.PositivePresentations
import all Section4.ValuePullback
import all Section4.Objects

/-! The scalar X acts by the positive unit line on the concrete residue
factor and by a signed value point on the concrete value factor. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {K F : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {JG JS J : Language} [JG.Structure (Additive O.ValueGroupˣ)] [JS.Structure (SignedValueGroup O)]
  [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (G : Submodule F (Additive O.ValueGroupˣ))
  (A : Set (SignedValueGroup O))
  (signedDef : ∀ {n} {D : Set (Fin n → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    A.Definable JS ((fun γ => positiveValueLabel O ∘ γ) '' D))

def positiveValueEmb : Additive O.ValueGroupˣ ↪ SignedValueGroup O := ⟨positiveValueLabel O,fun _ _ h => congrArg Prod.snd h⟩

def signedPieceMap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* SemiringOfSets (J := JS) A :=
  (embeddingMeasure (G : Set _) A (positiveValueEmb O) signedDef).descend

omit [Module F (Additive (PositiveRV O))] [LinearOrder K] [IsStrictOrderedRing K] in
theorem signedPieceMap_class {n} (D : Set (Fin n → Additive O.ValueGroupˣ)) (hd : (G : Set _).Definable JG D) :
    signedPieceMap O G A signedDef (pieceClass D hd) =
      pieceClass ((fun γ => positiveValueLabel O ∘ γ) '' D) (signedDef hd) :=
  PieceMeasure.descend_piece _ D hd

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem image_value_zero {n} : (fun γ : Fin n → Additive O.ValueGroupˣ => positiveValueLabel O ∘ γ) '' {0} =
    ({1} : Set (Fin n → SignedValueGroup O)) := Set.image_singleton

omit [Module F (Additive (PositiveRV O))] [LinearOrder K] [IsStrictOrderedRing K] in
include signedDef in
theorem signed_one_definable : A.Definable JS ({1} : Set (Fin 1 → SignedValueGroup O)) :=
  (image_value_zero O) ▸ signedDef (zeroTuple_definable (J := JG) G 1)

omit [Module F (Additive (PositiveRV O))] [LinearOrder K] [IsStrictOrderedRing K] in
theorem signedPieceMap_generator :
    signedPieceMap O G A signedDef (eValue (J := JG) G) =
      pieceClass {1} (signed_one_definable O G A signedDef) := by
  rw [eValue,signedPieceMap_class]
  have cong {D E : Set (Fin 1 → SignedValueGroup O)} (eq : D = E) (d : A.Definable JS D) (e : A.Definable JS E) :
      pieceClass D d = pieceClass E e := by subst E; rfl
  exact cong (image_value_zero O) _ _

include hv in
theorem unit_sharp_one {n} :
    sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) ({1} : Set (Fin n → SignedValueGroup O)) =
      unitSet O v (Equiv.refl (Fin n)) Set.univ := by
  rw [← image_value_zero O,signed_sharp_positive (J := J) O hO v hv P]
  ext x; constructor
  · rintro ⟨z,hz,rfl⟩
    change v ∘ z = 0 at hz
    let b (i : Fin n) : v.ker := ⟨z i,congrFun hz i⟩
    exact ⟨b,Set.mem_univ _,rfl⟩
  · rintro ⟨b,_,rfl⟩
    exact ⟨v.ker.subtype ∘ b,funext fun i => (b i).property,rfl⟩

variable (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp _ (signedLabel O hO) D))
include hv in
theorem residue_sharp_generator (he : A.Definable JS ({1} : Set (Fin 1 → SignedValueGroup O))) :
    residueClass (sharpObject _ S (signedLabel O hO) {1} (defSharp he)) (sharp_residue _ S (signedLabel O hO) A defSharp {1} (Set.finite_singleton _) he)
      = entireUnitWeight O v hv hO P S 1 := by
  apply residue_class_iso
  change RVDefinablyEquivalent _ S.carrier (sharp _ (signedLabel O hO) {1}) (unitSet O v (Equiv.refl (Fin 1)) Set.univ)
  rw [unit_sharp_one O v hv hO P]
  exact ⟨Equiv.refl _,definable_identity_label _ S (unit_univ_definable O v hv hO P S (Equiv.refl (Fin 1)))⟩

end GeneralizedEuler.Section4
