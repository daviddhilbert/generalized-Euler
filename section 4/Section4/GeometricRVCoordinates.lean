module

public import Section4.PiecewiseValueLift
public import Section4.ResidueEulerIsomorphism
public import Section4.ResidueLocalizationFormulas
public import Section4.SignedPuncturedIdeal
public import Section4.DistinguishedResiduePoint
public import Section4.Proposition421
import all Section4.RectangleEulerCoordinates
import all Section4.Factors
import all Section4.GradedEulerMaps
import all Section4.ValueEmbedding
import all Section4.ValueDescent
import all Section4.PositivePresentations
import all Section4.SignedTensorFactors
import all Section4.SignedRectangleFactors
import all Section4.RectangleMap
import all Section4.ValuePullback
import all Section4.ValueFactorMap
import all Section4.ResidueScissors
import all Section4.TaggedBoxPresentations
import all Section4.EulerRing
import all Section4.GeometricValuePresentation

/-! Remarks 4.23 and Proposition 4.24 for the actual fixed-base RV
and residue rings. The field inputs are the dimension--Euler classification
of residue sets and semilinearity in the ordered value space. -/
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
local instance finalEulerAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

local instance finalEulerSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) :=
  inferInstanceAs (JS.Structure (SignedValueGroup O))

variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (liftIso : ∀ {k} (D C : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS C →
    ∀ e : D ≃ C, A.Definable JS {w : Fin k ⊕ Fin k → SignedValueGroup O |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D) (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) C))
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
    (χ : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* Polynomial ℤ)
    (line : χ (residueClass
      (sharpObject (canonicalStructure (L := J) O hO P) S (signedLabel O hO) {1} (defSharp he))
      (sharp_residue (canonicalStructure (L := J) O hO P) S (signedLabel O hO) A defSharp {1}
        (Set.finite_singleton _) he)) = -Polynomial.X)
    (order : (G : Set (Additive O.ValueGroupˣ)).Definable JG {x : Fin 2 → Additive O.ValueGroupˣ | x 0 ≤ x 1})
    (bounded geometric : SemiringOfSets (J := JS) A →+* ℤ)
    (bp : bounded (pieceClass ({1} : Set (Fin 1 → SignedValueGroup O)) he) = 1)
    (br : bounded ((PieceMeasure.descend
      (embeddingMeasure (G : Set (Additive O.ValueGroupˣ)) A (positiveValueEmb O) signedDef)) (pieceClass _ L.ray)) = 0)
    (gp : geometric (pieceClass ({1} : Set (Fin 1 → SignedValueGroup O)) he) = 1)
    (gr : geometric ((PieceMeasure.descend
      (embeddingMeasure (G : Set (Additive O.ValueGroupˣ)) A (positiveValueEmb O) signedDef)) (pieceClass _ L.ray)) = -1)
    (semi : ∀ {k} (D : Set (Fin k → Additive O.ValueGroupˣ)), (G : Set _).Definable JG D → Polyhedral.SemilinearOver G D)


local notation "rvPoint" => residuePointObject O hO P S
local notation "resPt" => residueClass rvPoint (residuePoint_finite O hO P S lab)
local notation "idealValues" => allSigns (Z := SignTypeˣ) (lowerRay (V := Additive O.ValueGroupˣ))

include g agrees units clamp powers hv hs interpret witness primitives base reps minus qe sat rvSat χ line
  order bounded geometric bp br gp gr semi in
theorem geometric_rv_coordinates (classify : Function.Bijective (lift χ)) (singleton : χ resPt = Polynomial.X) :
    ∃ (C : SemiringGroupification.Ring (SemiringOfSets (J := JS) A) ≃+* valueRing)
      (c : EulerCoordinates res val χ C) (di : A.Definable JS idealValues),
      (∀ x, (C x).val=(GradedEuler.value A geometric x,GradedEuler.value A bounded x)) ∧
      c.equiv (1 + of _ (objectClass model S ⟨1,sharpObject model S lab idealValues (defSharp di)⟩) -
        of _ (objectClass model S ⟨1,rvPoint⟩)) = special := by
  have gen : σ (pieceClass _ L.point) = point := signedPieceMap_generator O G A signedDef
  let C := geometric_value_presentation L order A (1 : SignTypeˣ) interpret @semi geometric bounded
    (gen ▸ gp) gr (gen ▸ bp) br
  have coords (x) : (C x).val = (GradedEuler.value A geometric x,GradedEuler.value A bounded x) :=
    geometric_value_coordinates _ _ _ _ _ @semi _ _ _ _ _ _ _
  have pcoord : C (of _ point) = GeneralizedEuler.Section4.point := by
    apply Subtype.ext
    rw [coords]
    have f (ψ : SemiringOfSets (J := JS) A →+* ℤ) (h : ψ point=1) :
        GradedEuler.value A ψ (of _ point) = Polynomial.X := by
      have eq := GradedEuler.value_class A ψ (single ({1} : Set (Fin 1 → SignedValueGroup O)) he)
      change GradedEuler.value A ψ (of _ point) = Polynomial.C (ψ point) * Polynomial.X^1 at eq
      simpa [h] using eq
    exact Prod.ext (f geometric gp) (f bounded bp)
  have rcoord : C (of _ (σ (pieceClass _ L.ray)))=ray :=
    geometric_value_ray L order A (1 : SignTypeˣ) interpret @semi geometric bounded (gen ▸ gp) gr (gen ▸ bp) br
  have bij := proposition_4_21 O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso
    @interpret he @witness primitives base reps minus (fun φ => qe φ) sat @rvSat
  let c := rectangle_euler_coordinates res val torus point (balance_finite_value model S lab A defSharp liftIso {1} (Set.finite_singleton _) he)
    χ line bij classify C pcoord
  obtain ⟨di,ei⟩ := punctured_value_class L A (1 : SignTypeˣ) interpret (by decide)
  change pieceClass idealValues di = σ (pieceClass _ L.ray) + σ (pieceClass _ L.ray) at ei
  refine ⟨C,c,di,coords,?_⟩
  rw [← valueFactorHom_piece model S lab A defSharp liftIso idealValues di,
    ← includeResidue_class rvPoint (residuePoint_finite O hO P S lab),ei]
  simpa only [EulerCoordinates.specialClass] using c.special_image _ rcoord _ singleton

/-- The special quotient, integer characters, and normalized homogeneous
formulas for the two geometric residue localizations. -/
abbrev SectionFourEulerFormulas (ordinary : ResidueSemiring model S lab →+* ℤ) : Prop :=
    ∃ di : A.Definable JS idealValues,
      let u := 1 + of _ (objectClass model S ⟨1,sharpObject model S lab idealValues (defSharp di)⟩) -
        of _ (objectClass model S ⟨1,rvPoint⟩)
      (∃ q : (SemiringGroupification.Ring (RVSemiring model S) ⧸ Ideal.span {u}) ≃+* ℤ × ℤ,
        ∀ f : (SemiringGroupification.Ring (RVSemiring model S) ⧸ Ideal.span {u}) →+* ℤ,
          f=(RingHom.fst ℤ ℤ).comp q.toRingHom ∨ f=(RingHom.snd ℤ ℤ).comp q.toRingHom) ∧
      ∀ choice : EulerChoice, let d := residueDenominator torus resPt choice
        ∃ f : SemiringGroupification.Ring (RVSemiring model S) →+* Localization.Away d,
          Set.range f = Set.range (Int.castRingHom (Localization.Away d)) ∧ f u=0 ∧
          ∀ (x : SemiringGroupification.Ring (ResidueSemiring model S lab)) (k : ℕ) (a : ℤ),
            GradedEuler.residue model S lab ordinary x=Polynomial.C a*Polynomial.X^k →
            f (SemiringGroupification.map res x)=algebraMap _ (Localization.Away d) x * (IsLocalization.Away.invSelf d)^k

include g agrees units clamp powers hv hs interpret liftIso witness primitives base reps minus qe sat rvSat
  order bounded geometric bp br gp gr semi in
theorem section_four_euler_maps (ordinary : ResidueSemiring model S lab →+* ℤ)
    (classification : ResidueEulerClassification (M := model) (S := S) lab ordinary)
    (unitLine : ordinary torus = -1) (singleton : ordinary resPt = 1) :
    SectionFourEulerFormulas O hO P S A @defSharp he ordinary := by
  let χ := GradedEuler.polynomialMeasure _ _ (GradedEuler.residue_homogeneous model S lab) ordinary
  have cls {k} (U : RVObject model S k) (hu : U.IsResidue model S lab) :
      χ (residueClass U hu)=Polynomial.C (ordinary (residueClass U hu))*Polynomial.X^k :=
    GradedEuler.polynomialMeasure_X _ _ (GradedEuler.residue_homogeneous model S lab) ordinary ⟨⟨k,U⟩,hu⟩
  have hp : χ resPt=Polynomial.X := by rw [cls,singleton]; simp
  have ht : χ torus= -Polynomial.X := by rw [cls,unitLine]; simp
  have bij : Function.Bijective (lift χ) := classification.polynomial_bijective resPt
    (residueDegree_class (M := model) (S := S) lab _ _) singleton hp
  obtain ⟨C,c,di,_,specialEq⟩ := geometric_rv_coordinates O v hv s hs G B hO P g agrees units clamp powers
    S A defSharp liftIso @interpret he L signedDef witness primitives base reps minus @qe sat rvSat χ ht order
    bounded geometric bp br gp gr @semi bij hp
  exact ⟨di,⟨c.quotient _ specialEq,c.characters _ specialEq⟩,
    c.localized_formulas bij torus resPt ht hp _ specialEq⟩

include g agrees units clamp powers hv hs interpret witness primitives base reps minus qe sat rvSat
  order bounded geometric bp br gp gr semi in
theorem section_four_euler_maps_from_affine_partitions
    (affine : HasSignedAffinePartitions (JG := JG) (JS := JS) G A)
    (ordinary : ResidueSemiring model S lab →+* ℤ)
    (classification : ResidueEulerClassification (M := model) (S := S) lab ordinary)
    (unitLine : ordinary torus = -1) (singleton : ordinary resPt = 1) :
    SectionFourEulerFormulas O hO P S A @defSharp he ordinary :=
  section_four_euler_maps O v hv s hs G B hO P g agrees units clamp powers S A defSharp
    (fun {_} => value_morphism_lift O hO P S v hv s hs powers G A reps @interpret @defSharp @witness affine)
    @interpret he L signedDef witness primitives base reps minus @qe sat rvSat order bounded geometric
    bp br gp gr @semi ordinary classification unitLine singleton

end GeneralizedEuler.Section4
