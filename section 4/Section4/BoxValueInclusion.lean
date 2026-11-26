module

public import Section4.BoxResidueCancellation
public import Section4.ArbitraryBoxUnions
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

/-! The concrete RV lift is injective on all finite unions of padded boxes
in every ambient degree. Multiplication by an arbitrary nonzero-Euler
residue object still gives an injective map on these classes. -/
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
local instance rawBoxGroupAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

local instance rawBoxGroupSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) :=
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

include g agrees units clamp powers hv hs interpret in
set_option maxHeartbeats 1800000 in
theorem cancel_residue_on_arbitrary_box_unions
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

    {k : ℕ} (D E : Presentation G k) (oldStep : step ∈ G)
    (eq : objectClass model S ⟨i,R⟩ * val (σ (presentationValue L D)) =
      objectClass model S ⟨i,R⟩ * val (σ (presentationValue L E))) :
    σ (presentationValue L D) = σ (presentationValue L E) := by
  cases k with
  | zero =>
    have bij := proposition_4_21 O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso
      @interpret he @witness primitives base reps minus (fun φ => qe φ) sat @rvSat
    have balance := balance_finite_value model S lab A defSharp liftIso {1} (Set.finite_singleton _) he
    rw [← includeResidue_class R residue] at eq
    have ec := SemiringGroupification.cancel_residue_euler res val torus point balance χ line bij (residueClass R residue)
      _ _ i z nz poly eq (SemiringGroupification.lift bounded) (by simpa using bp)
    simp only [presentationValue_zero,map_natCast] at ec
    simp only [presentationValue_zero,map_natCast]
    exact congrArg Nat.cast (Int.ofNat_inj.mp ec)
  | succ k =>
    obtain ⟨n,alphabet,a,b,ha,hb⟩ := normalize_presentations L D E step oldStep positive
    let boxes {m} (x : Fin m → Fin (k+1) → Fin (n+3)) := taggedBoxes alphabet L A (positiveValueEmb O) signedDef x
    have image {m} (x : Fin m → Fin (k+1) → Fin (n+3)) :
        taggedValueClass A (boxes x) = σ (unionValue alphabet L x) := taggedBoxes_class _ _ _ _ _ _
    rw [ha,hb,← image a,← image b] at eq ⊢
    exact cancel_residue_on_box_presentations O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso @interpret he
      alphabet L signedDef witness primitives base reps minus @qe sat rvSat χ line order step positive satUnary
      bounded geometric bp br gp gr R residue z nz poly k a b eq

include g agrees units clamp powers hv hs interpret in
set_option maxHeartbeats 1800000 in
theorem value_injective_on_arbitrary_box_unions
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

    {k : ℕ} (D E : Presentation G k) (oldStep : step ∈ G)
    (eq : val (σ (presentationValue L D)) = val (σ (presentationValue L E))) :
    σ (presentationValue L D) = σ (presentationValue L E) := by
  let T := sharpObject model S lab {1} (defSharp he)
  have finite : T.IsResidue model S lab := sharp_residue model S lab A defSharp {1} (Set.finite_singleton _) he
  have hχ : χ (residueClass T finite) = Polynomial.C (-1) * Polynomial.X ^ 1 := by simpa using line
  exact cancel_residue_on_arbitrary_box_unions O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso @interpret he
    L signedDef witness primitives base reps minus @qe sat rvSat χ line order step positive satUnary
    bounded geometric bp br gp gr T finite (-1) (by decide) hχ D E oldStep (congrArg (objectClass model S ⟨1,T⟩ * ·) eq)

end GeneralizedEuler.Section4
