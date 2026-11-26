module

public import Section4.Proposition421
public import Section4.GroupifiedRectangle
import all Section4.RectangleMap
import all Section4.ResidueScissors
import all Section4.ValueFactorMap
import all Section4.Factors

/-! The split injection after Question 4.16 for the groupifications of
the actual value and RV scissor semirings, with the signed Euler formula
and the consequence of the residue classification of Remark 4.8. -/
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
local instance concreteGroupAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

local instance concreteGroupSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) :=
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

include g agrees units clamp powers hv hs interpret in
set_option maxHeartbeats 1800000 in
theorem groupified_value_inclusion
    (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
    (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
      (fun e γ => (e • Additive.ofMul γ).toMul) P)
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ (G : Set (Additive O.ValueGroupˣ)) ∧
      ((linearValueSection v hv s hs).encode t.val).2 ∈ B)
    (reps : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
    (minus : rv O (-1) ∈ S.carrier .rv)
    (qe : ∀ {n} (φ : SortedFormula J F (FullRVVariables S (Fin n))), ∃ q : SortedFormula J F (FullRVVariables S (Fin n)), q.IsQF ∧
      ∀ x, q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)
    (sat : ∀ m (Δ : Set (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m))),
      (∀ t : Finset (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin m)), (↑t : Set _) ⊆ Δ →
        ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ t, φ.Realize x) →
      ∃ x : Fin m → Additive O.ValueGroupˣ, ∀ φ ∈ Δ, φ.Realize x)
    (rvSat : ∀ {n} (D : ℕ → Set (Fin n → RV0 O)), (∀ i, isRVSet _ S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (χ : ResidueSemiring model S lab →+* Polynomial ℤ) (line : χ torus = -Polynomial.X) :
    (∃ ρ : SemiringGroupification.Ring (RVSemiring model S) →+* SemiringGroupification.Ring (SemiringOfSets (J := JS) A),
      ρ.comp (SemiringGroupification.map val) = RingHom.id _ ∧
      ∀ a b (i : ℕ) (z : ℤ), χ a = Polynomial.C z * Polynomial.X^i →
        ρ (SemiringGroupification.of _ (res a * val b)) =
          (-1)^i * (z : SemiringGroupification.Ring (SemiringOfSets (J := JS) A)) *
          (SemiringGroupification.of _ point)^i * SemiringGroupification.of _ b) ∧
    Function.Injective (SemiringGroupification.map val) ∧
    (Function.Bijective (SemiringGroupification.lift χ) → Function.Bijective (SemiringGroupification.map val)) := by
  have balanced := balance_finite_value model S lab A defSharp liftIso ({1} : Set (Fin 1 → SignedValueGroup O)) (Set.finite_singleton _) he
  have bij := proposition_4_21 O v hv s hs G B hO P g agrees units clamp powers S A defSharp liftIso
    @interpret he @witness primitives base reps minus @qe sat @rvSat
  exact ⟨⟨rectangleRetraction res val torus point balanced χ line bij,
      groupified_value_retracts res val torus point balanced χ line bij,
      rectangleRetraction_homogeneous res val torus point balanced χ line bij⟩,
    groupified_value_map_injective res val torus point balanced χ line bij,
    groupified_value_map_bijective res val torus point balanced χ line bij⟩

end GeneralizedEuler.Section4
