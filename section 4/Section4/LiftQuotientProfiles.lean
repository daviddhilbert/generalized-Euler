module

public import Section4.QuotientSpanProfiles
public import Section4.CanonicalRectangles
import all Section4.SignedShears
import all Section4.RVTaggedEquivalence
import all Section4.Factors

/-! Equal classes of tagged sharp sets have identical profiles of
coordinate spans for any family of quotient spaces over the fixed base. -/
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
  {J JS : Language} [J.Structure K] [J.Structure (Residue O)]
  [JS.Structure (SignedValueGroup O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (liftIso : ∀ {k} (D E : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS E →
    ∀ f : D ≃ E, A.Definable JS {z : Fin k ⊕ Fin k → SignedValueGroup O | ∃ x : D, x.val = z ∘ Sum.inl ∧ (f x).val = z ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D) (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) E))
local notation "M" => canonicalStructure (L := J) O hO P
local notation "val" => signedLabel O hO
local notation "sh" => taggedSharp (S := S) val A defSharp

include hv hs agrees units clamp powers in
theorem quotient_profiles_of_lift_iso
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)),
      ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    {k l : ℕ} (U : Over (J := JS) A k) (W : Over (J := JS) A l)
    (iso : (sh U).Iso (sh W))
    {I : Type*} (H : I → Submodule F (Additive O.ValueGroupˣ)) (extendsBase : ∀ i, G ≤ H i) :
    Set.range (fun a : U.points A => fun i => quotientTupleSpan (H i) (unsignedPoint O A U a)) =
    Set.range (fun b : W.points A => fun i => quotientTupleSpan (H i) (unsignedPoint O A W b)) := by
  obtain ⟨f,hf⟩ := iso
  have cover {m n : ℕ} (D : Over (J := JS) A m) (E : Over (J := JS) A n) (q : (sh D).Points ≃ (sh E).Points)
      (graph : ∀ i j, isRVSet M S (RVFamily.graphPiece _ _ q i j)) (a : D.points A) :
      ∃ b : E.points A, ∀ i, quotientTupleSpan (H i) (unsignedPoint O A D a) =
        quotientTupleSpan (H i) (unsignedPoint O A E b) := by
    have action (i j L' z) (hz : z ∈ RVFamily.graphPiece _ _ q i j) :=
      ((signedShear_reduct (J := J) v hv s hs G L' hO g P agrees units clamp powers).setInvariant S
        (fun t => signedShear_base v hv s hs G L' _ (base t)) qe (graph i j) z).mpr hz
    obtain ⟨b,h⟩ := signed_label_quotient_spans O hO v hv s hs G P S A defSharp D E q action a
    exact ⟨b,fun i => h _ (extendsBase i)⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨a,rfl⟩
    obtain ⟨b,h⟩ := cover U W f hf a
    exact ⟨b,(funext h).symm⟩
  · rintro _ ⟨b,rfl⟩
    obtain ⟨a,h⟩ := cover W U f.symm (RVFamily.inverse_graph _ _ f hf) b
    exact ⟨a,(funext h).symm⟩

include hv hs agrees units clamp powers in
theorem quotient_profiles_of_lift_equality
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)),
      ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    {k : ℕ} (U W : Over (J := JS) A k)
    (eq : valueFactorHom M S val A defSharp liftIso (taggedValueClass A U) =
      valueFactorHom M S val A defSharp liftIso (taggedValueClass A W))
    {I : Type*} (H : I → Submodule F (Additive O.ValueGroupˣ)) (extendsBase : ∀ i, G ≤ H i) :
    Set.range (fun a : U.points A => fun i => quotientTupleSpan (H i) (unsignedPoint O A U a)) =
    Set.range (fun b : W.points A => fun i => quotientTupleSpan (H i) (unsignedPoint O A W b)) := by
  exact quotient_profiles_of_lift_iso O v hv s hs G hO P g agrees units clamp powers S A defSharp
    base qe U W (tagged_lift_iso_of_class_eq (S := S) val A defSharp liftIso U W eq) H extendsBase

end GeneralizedEuler.Section4
