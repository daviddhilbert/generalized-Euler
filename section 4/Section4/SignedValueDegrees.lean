module

public import Section4.ValueDegrees
public import Section4.SignedTensorFactors
public import Section4.SignedValueGeneration
import all Section4.SignedValueGeneration
import all Section4.SignedRectangleFactors

/-! Lemma 4.14 in the tagged signed category. Each value frame records
an independent point in its free domain. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] (O : ValuationSubring K)
  [Module F (Additive O.ValueGroupˣ)] {JG JS : Language}
  [JG.Structure (Additive O.ValueGroupˣ)] [JS.Structure (SignedValueGroup O)]
  (G : Submodule F (Additive O.ValueGroupˣ)) (A : Set (SignedValueGroup O))
local instance signedDegreeSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) := inferInstanceAs (JS.Structure (SignedValueGroup O))
variable (interpret : SignedInterpretation (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A)

include interpret in
theorem tagged_value_degree_decomposition {k} (U : Over (J := JS) A k)
    (h : ValueLanguage (J := JG) G)
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D)) :
    let positive : ∀ {n} {D : Set (Fin n → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
      A.Definable JS ((fun γ => positiveValueLabel O ∘ γ) '' D) := by
        intro n D hd
        exact signed_stratum_definable _ _ @interpret (fun _ => (1 : SignTypeˣ)) _ hd
    let σ := signedPieceMap (JG := JG) (JS := JS) O G A @positive
    let point := pieceClass {1} (signed_one_definable (JG := JG) (JS := JS) O G A @positive)
    ∃ (l : Fin U.tags → (Fin k → SignTypeˣ) → ℕ)
      (d : ∀ i b, Fin (l i b) → DefinablePiece JG G k),
      taggedValueClass A U = ∑ i, ∑ b, ∑ j, σ (pieceClass _ (d i b j).definable) *
        point^(k-(d i b j).rank) := by
  intro positive σ point
  let B i b := signInsert b ⁻¹' U.piece i
  have defB i b : (G : Set (Additive O.ValueGroupˣ)).Definable JG (B i b) := (interpret _).mp (U.isDefinable i) b
  choose l d _ _ eq using fun i b => piece_degree_decomposition h sat (B i b) (defB i b)
  refine ⟨l,d,?_⟩
  rw [taggedValueClass_eq_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [signed_piece_decomposition _ _ (1 : SignTypeˣ) @interpret _ (U.isDefinable i)]
  apply Finset.sum_congr rfl; intro b _
  calc _ = σ (pieceClass _ (defB i b)) := (signedPieceMap_class (JG := JG) (JS := JS) O G A @positive _ _).symm
       _ = _ := by
         rw [eq,map_sum]
         apply Finset.sum_congr rfl; intro j _
         rw [map_mul,map_pow]
         congr 2
         exact signedPieceMap_generator (JG := JG) (JS := JS) O G A @positive

end GeneralizedEuler.Section4
