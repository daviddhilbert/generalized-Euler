module

public import Section4.ArbitraryBoxUnions
public import Section4.SignedValueGeneration
import all Section4.ArbitraryBoxUnions
import all Section4.SignedValueGeneration
import all Section4.ValueEmbedding
import all Section4.TaggedValueClasses
import all Section4.ValueDescent

/-! Adding finite presentations and passing from unsigned pieces to
signed tagged value objects in their original degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open FirstOrder Set ValueObject
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [AddCommGroup V] [LinearOrder V]
  [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V] {J : Language} [J.Structure V]
  {G : Submodule F V} (L : BoxLanguage (J := J) G) {k : ℕ}

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem sum_presentations {I : Type} [Fintype I] (p : I → Presentation G k) :
    ∃ q : Presentation G k, presentationValue L q = ∑ i, presentationValue L (p i) := by
  classical
  let T := (i : I) × Fin (p i).tags
  let tags := (Fintype.equivFin T).symm
  let q : Presentation G k := ⟨_,fun t => (p (tags t).1).axes (tags t).2,fun t => (p (tags t).1).widths (tags t).2⟩
  let w (t : T) := pieceClass _ (coordinateBox_definable _ (fun j => unary_definable L ((p t.1).axes t.2 j)
    (fun b h => ((p t.1).widths t.2 j b h).1)))
  refine ⟨q,(Equiv.sum_comp tags w).trans ?_⟩
  exact Fintype.sum_sigma _

variable {Z : Type} [Fintype Z] {H : Language} [H.Structure (Z × V)] (A : Set (Z × V)) (one : Z)
  (interpret : SignedInterpretation (J := J) (H := H) (G : Set V) A)

def insertPositive : V ↪ Z × V := ⟨fun x => (one,x),fun _ _ h => congrArg Prod.snd h⟩

def signedPresentationMap : SemiringOfSets (J := J) (G : Set V) →+* SemiringOfSets (J := H) A :=
  (embeddingMeasure (G : Set V) A (insertPositive one)
    (fun h => signed_stratum_definable (G : Set V) A interpret (fun _ => one) _ h)).descend

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem present_tagged {k} (U : Over (J := H) A k)
    (decompose : ∀ (D : Set (Fin k → V)) (hd : (G : Set V).Definable J D),
      ∃ p : Presentation G k, presentationValue L p = pieceClass D hd) :
    ∃ p : Presentation G k, signedPresentationMap (G := G) A one interpret (presentationValue L p) = taggedValueClass A U := by
  classical
  let cell (i : Fin U.tags) (b : Fin k → Z) := signInsert b ⁻¹' U.piece i
  let defCell (i : Fin U.tags) (b : Fin k → Z) := (interpret _).mp (U.isDefinable i) b
  choose p eq using fun i b => decompose (cell i b) (defCell i b)
  let σ := signedPresentationMap (G := G) A one interpret
  have signed (i : Fin U.tags) (b : Fin k → Z) : σ (presentationValue L (p i b)) =
      pieceClass (signInsert (fun _ => one) '' cell i b)
        (signed_stratum_definable (G : Set V) A interpret _ _ (defCell i b)) := by
    rw [eq]
    exact PieceMeasure.descend_piece _ _ _
  obtain ⟨q,hq⟩ := sum_presentations L (fun t : Fin U.tags × (Fin k → Z) => p t.1 t.2)
  refine ⟨q,?_⟩
  change σ _ = _
  rw [hq,map_sum,Fintype.sum_prod_type,taggedValueClass_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [signed_piece_decomposition (G : Set V) A one interpret (U.piece i) (U.isDefinable i)]
  exact Finset.sum_congr rfl fun b _ => signed i b

end GeneralizedEuler.Section4.PaddedBox
