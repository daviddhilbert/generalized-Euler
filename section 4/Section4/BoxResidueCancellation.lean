module

public import Section4.TaggedBoxComparison
public import Section4.ResidueCancellation
public import Section4.Proposition421
import all Section4.BoxPresentations
import all Section4.ValueEmbedding
import all Section4.SignedTensorFactors
import all Section4.ValuePadding
import all Section4.SignedRectangleFactors
public import Section4.GroupifiedRectangle
import all Section4.RectangleMap
import all Section4.ResidueScissors
import all Section4.ValueFactorMap
import all Section4.Factors

/-! Nonzero residue Euler characteristic gives cancellation on all tagged
box presentations, using the actual tensor theorem and two value Euler maps. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
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
local instance boxGroupAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

local instance boxGroupSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) :=
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
variable {C : Type*} [LinearOrder C] [BoundedOrder C] [Nontrivial C] [Fintype C]
  [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F (Additive O.ValueGroupˣ)]
  (alphabet : Alphabet G C) (L : BoxLanguage (J := JG) G)
  (signedDef : ∀ {n} {D : Set (Fin n → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    A.Definable JS (mapTuples (positiveValueEmb O) '' D))
local notation "boxes" => taggedBoxes alphabet L A (positiveValueEmb O) signedDef
local notation "σ" => PieceMeasure.descend (embeddingMeasure (G : Set (Additive O.ValueGroupˣ)) A (positiveValueEmb O) signedDef)

include g agrees units clamp powers hv hs interpret in
set_option maxHeartbeats 1800000 in
theorem cancel_residue_on_box_presentations
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
    (χ : ResidueSemiring model S lab →+* Polynomial ℤ) (line : χ torus = -Polynomial.X)
    (order : (G : Set (Additive O.ValueGroupˣ)).Definable JG {x : Fin 2 → Additive O.ValueGroupˣ | x 0 ≤ x 1})
    (step : Additive O.ValueGroupˣ) (positive : 0 < step)
    (satUnary : ∀ fs : Finset (Additive O.ValueGroupˣ), UnaryValueSaturation JG (↑(G ⊔ Submodule.span F (fs : Set (Additive O.ValueGroupˣ))) : Set (Additive O.ValueGroupˣ)))
    (bounded geometric : SemiringOfSets (J := JS) A →+* ℤ)
    (bp : bounded point = 1) (br : bounded (σ (pieceClass _ L.ray)) = 0)
    (gp : geometric point = 1) (gr : geometric (σ (pieceClass _ L.ray)) = -1)
    {i : ℕ} (R : RVObject model S i) (residue : R.IsResidue model S lab)
    (z : ℤ) (nz : z ≠ 0) (poly : χ (residueClass R residue) = Polynomial.C z * Polynomial.X^i)
    (k : ℕ) {m n} (a : Fin m → Fin (k+1) → C) (b : Fin n → Fin (k+1) → C)
    (eq : objectClass model S ⟨i,R⟩ * val (taggedValueClass A (boxes a)) =
      objectClass model S ⟨i,R⟩ * val (taggedValueClass A (boxes b))) :
    taggedValueClass A (boxes a) = taggedValueClass A (boxes b) := by
  have nonempty : R.carrier.Nonempty := by
    by_contra empty
    rw [residue_class_zero R residue (Set.not_nonempty_iff_eq_empty.mp empty),map_zero] at poly
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr nz) (pow_ne_zero i Polynomial.X_ne_zero)) poly.symm
  have bij := proposition_4_21 O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso
    @interpret he @witness primitives base reps minus (fun φ => qe φ) sat @rvSat
  have balance := balance_finite_value model S lab A defSharp liftIso {1} (Set.finite_singleton _) he
  have withRes := eq
  rw [← includeResidue_class R residue] at withRes
  have cancel (ψ : SemiringOfSets (J := JS) A →+* ℤ) (pt : ψ point = 1) :
      ψ (taggedValueClass A (boxes a)) = ψ (taggedValueClass A (boxes b)) := by
    simpa only [SemiringGroupification.lift_of] using
      SemiringGroupification.cancel_residue_euler res val torus point balance χ line bij (residueClass R residue)
        _ _ i z nz poly withRes (SemiringGroupification.lift ψ) (by simpa using pt)
  have pointEq : σ (pieceClass _ L.point) = point :=
    signedPieceMap_generator O G A signedDef
  exact compare_tagged_box_products O v hv s hs G hO P g agrees units clamp powers S A defSharp liftIso
    alphabet L signedDef (fun t => (base t).1) @qe order step positive satUnary k a b R residue nonempty witness eq
    bounded geometric (pointEq ▸ bp) br (pointEq ▸ gp) gr (cancel _ bp) (cancel _ gp)

end GeneralizedEuler.Section4
