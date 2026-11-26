module

public import Section4.BoxValueInclusion
public import Section4.HomogeneousBoxDecomposition
import all Section4.TaggedBoxPresentations
import all Section4.SignedTensorFactors
import all Section4.SignedRectangleFactors
import all Section4.HomogeneousValueLift

/-! The positive value map in every ambient degree, and cancellation by
a residue object of nonzero Euler characteristic. The semilinearity input
is the fixed-base description of value-definable sets. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))
  {J JG JH JS : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure O.ValueGroupˣ]
  [JH.Structure (Residue O)] [JS.Structure (SignedValueGroup O)]
  (B : Set (Residue O)) (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
open SemiringGroupification
open scoped TensorProduct
local instance degreeValueAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

local instance degreeValueSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) :=
  inferInstanceAs (JS.Structure (SignedValueGroup O))

variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp _ (signedLabel O hO) D))
  (liftIso : ∀ {k} (D C : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS C →
    ∀ e : D ≃ C, A.Definable JS {w : Fin k ⊕ Fin k → SignedValueGroup O |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp _ (signedLabel O hO) D) (sharp _ (signedLabel O hO) C))
  (interpret : SignedInterpretation (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A)
  (he : A.Definable JS ({1} : Set (Fin 1 → SignedValueGroup O)))
local notation "model" => canonicalStructure (L := J) O hO P
local notation "lab" => signedLabel O hO
local notation "res" => includeResidue model S lab
local notation "val" => valueFactorHom model S lab A defSharp liftIso
local notation "point" => pieceClass ({1} : Set (Fin 1 → SignedValueGroup O)) he
local notation "torus" => residueClass (sharpObject model S lab {1} (defSharp he))
  (sharp_residue model S lab A defSharp {1} (Set.finite_singleton _) he)


open PaddedBox
variable [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F (Additive O.ValueGroupˣ)]
  (L : BoxLanguage (J := JG) G)
  (signedDef : ∀ {n} {D : Set (Fin n → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    A.Definable JS (mapTuples (positiveValueEmb O) '' D))
local notation "σ" => PieceMeasure.descend (embeddingMeasure (G : Set (Additive O.ValueGroupˣ)) A (positiveValueEmb O) signedDef)

variable
    (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
    (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
      (fun e γ => (e • Additive.ofMul γ).toMul) P)
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ (G : Set (Additive O.ValueGroupˣ)) ∧
      ((linearValueSection v hv s hs).encode t.val).2 ∈ B)
    (reps : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
    (minus : rv O (-1) ∈ S.carrier .rv)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)), ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧
      ∀ x, q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)
    (sat : ∀ m (Δ : Set (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m))),
      (∀ t : Finset (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m)), (↑t : Set _) ⊆ Δ →
        ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ t, φ.Realize x) →
      ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ Δ, φ.Realize x)
    (rvSat : ∀ {n} (D : ℕ → Set (Fin n → RV0 O)), (∀ i, isRVSet _ S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (χ : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* Polynomial ℤ) (line : χ (residueClass (sharpObject (canonicalStructure (L := J) O hO P) S (signedLabel O hO) {1} (defSharp he))
  (sharp_residue (canonicalStructure (L := J) O hO P) S (signedLabel O hO) A defSharp {1} (Set.finite_singleton _) he)) = -Polynomial.X)
    (order : (G : Set (Additive O.ValueGroupˣ)).Definable JG {x : Fin 2 → Additive O.ValueGroupˣ | x 0 ≤ x 1})
    (step : Additive O.ValueGroupˣ) (positive : 0 < step)
    (satUnary : ∀ fs : Finset (Additive O.ValueGroupˣ), UnaryValueSaturation JG (↑(G ⊔ Submodule.span F (fs : Set (Additive O.ValueGroupˣ))) : Set (Additive O.ValueGroupˣ)))
    (bounded geometric : SemiringOfSets (J := JS) A →+* ℤ)
    (bp : bounded (pieceClass ({1} : Set (Fin 1 → SignedValueGroup O)) he) = 1) (br : bounded ((PieceMeasure.descend (embeddingMeasure (G : Set (Additive O.ValueGroupˣ)) A (positiveValueEmb O) signedDef)) (pieceClass _ L.ray)) = 0)
    (gp : geometric (pieceClass ({1} : Set (Fin 1 → SignedValueGroup O)) he) = 1) (gr : geometric ((PieceMeasure.descend (embeddingMeasure (G : Set (Additive O.ValueGroupˣ)) A (positiveValueEmb O) signedDef)) (pieceClass _ L.ray)) = -1)
    (oldStep : step ∈ G)
    (semi : ∀ {k} (D : Set (Fin k → Additive O.ValueGroupˣ)), (G : Set _).Definable JG D → Polyhedral.SemilinearOver G D)

omit [LinearOrder K] [IsStrictOrderedRing K] [Module F (Additive (PositiveRV O))] in
include L order interpret semi in
private theorem signed_boxes {k : ℕ} (x : homogeneousValue (J := JS) A k) :
    ∃ p : Presentation G k, σ (presentationValue L p) = x.val :=
  homogeneous_box_presentation L order A (1 : SignTypeˣ) interpret semi x

include g agrees units clamp powers hv hs interpret witness primitives base reps minus qe sat rvSat χ line
  order step positive satUnary bounded geometric bp br gp gr oldStep semi in
theorem nonzero_euler_residue_cancellation {i : ℕ} (R : RVObject model S i) (residue : R.IsResidue model S lab)
    (z : ℤ) (nz : z ≠ 0) (poly : χ (residueClass R residue) = Polynomial.C z * Polynomial.X^i) (k : ℕ) :
    Function.Injective (fun x : homogeneousValue (J := JS) A k => objectClass model S ⟨i,R⟩ * val x.val) := by
  intro x y eq
  obtain ⟨D,dx⟩ := signed_boxes O G A interpret L signedDef order @semi x
  obtain ⟨E,ey⟩ := signed_boxes O G A interpret L signedDef order @semi y
  apply Subtype.ext
  dsimp only at eq
  rw [← dx,← ey] at eq ⊢
  exact cancel_residue_on_arbitrary_box_unions O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso
    @interpret he L signedDef witness primitives base reps minus @qe sat rvSat χ line order step positive satUnary
    bounded geometric bp br gp gr R residue z nz poly D E oldStep eq

include g agrees units clamp powers hv hs interpret witness primitives base reps minus qe sat rvSat χ line
  order step positive satUnary bounded geometric bp br gp gr oldStep semi in
theorem all_degree_value_injective (k : ℕ) :
    Function.Injective (homogeneousValueLift A model S lab defSharp liftIso k) := by
  intro x y eq
  obtain ⟨D,dx⟩ := signed_boxes O G A interpret L signedDef order @semi x
  obtain ⟨E,ey⟩ := signed_boxes O G A interpret L signedDef order @semi y
  have same : val x.val = val y.val := congrArg Subtype.val eq
  apply Subtype.ext
  rw [← dx,← ey] at same ⊢
  exact value_injective_on_arbitrary_box_unions O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso
    @interpret he L signedDef witness primitives base reps minus @qe sat rvSat χ line order step positive satUnary
    bounded geometric bp br gp gr D E oldStep same

end GeneralizedEuler.Section4
