module

public import Section4.ResidueEulerMeasure
public import Section4.DegreeOneMatching
public import Section4.CanonicalRectangles
import all Section4.SignedShears
import all Section4.SignedWholeMatches
import all Section4.SignedValueReflection
import all Section4.TaggedMatchGraph
import all Section4.UnaryTaggedComparison
import all Section4.Factors
import all Section2.SortedStructure
import all Section4.ValuePullback

/-! Degree one of the partial answer to Question 4.16. Equality in the
actual RV semiring implies equality of the original tagged value classes. -/
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
local instance degreeOneAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) := inferInstanceAs (JG.Structure O.ValueGroupˣ)
local instance degreeOneSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) := inferInstanceAs (JS.Structure (SignedValueGroup O))
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
local notation "lab" => sharpLabel (S := S) val A defSharp

include hv hs agrees units clamp powers in
theorem degree_one_value_injective
    (interpret : SignedInterpretation (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A)
    (he : A.Definable JS ({1} : Set (Fin 1 → SignedValueGroup O)))
    (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO (G : Set (Additive O.ValueGroupˣ)) B
      (fun e γ => (e • Additive.ofMul γ).toMul) P)
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ (G : Set (Additive O.ValueGroupˣ)) ∧
      ((linearValueSection v hv s hs).encode t.val).2 ∈ B)
    (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet M S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)), ∃ q : SortedFormula J F (FullRVVariables S I),
      q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    (sat : ∀ n (Δ : Set (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin n))),
      (∀ t : Finset (JG[[(G : Set (Additive O.ValueGroupˣ))]].Formula (Fin n)), (↑t : Set _) ⊆ Δ →
        ∃ x : Fin n → Additive O.ValueGroupˣ, ∀ φ ∈ t, φ.Realize x) →
      ∃ x : Fin n → Additive O.ValueGroupˣ, ∀ φ ∈ Δ, φ.Realize x)
    (χ : UnaryEuler JH B)
    (ray : ∀ h : B.Definable JH (residuePositiveRay O hO), χ.weight _ h = -1)
    (U W : Over (J := JS) A 1)
    (eq : valueFactorHom M S val A defSharp liftIso (taggedValueClass A U) =
      valueFactorHom M S val A defSharp liftIso (taggedValueClass A W)) : taggedValueClass A U = taggedValueClass A W := by
  obtain ⟨f,graph⟩ := tagged_lift_iso_of_class_eq (S := S) val A defSharp liftIso U W eq
  let T := linearValueSection v hv s hs
  let pow (e : F) (γ : O.ValueGroupˣ) := (e • Additive.ofMul γ).toMul
  have hsec (e γ) : P e (T.representative γ) = T.representative (pow e γ) :=
    (powers e _).symm.trans (congrArg (fun x : Additive (PositiveRV O) => positiveRVToRV0 O x.toMul) (s.map_smul e _).symm)
  have reflect (D : Set (Fin 1 ⊕ Fin 1 → SignedValueGroup O)) :=
    signed_value_reflection O hO P S T (G : Set (Additive O.ValueGroupˣ)) B A @interpret pow primitives g agrees clamp units hsec D qe base
  have inv := RVFamily.inverse_graph _ _ f graph
  have action (V Y : Over (J := JS) A 1) (q : (sh V).Points ≃ (sh Y).Points)
      (defG : ∀ i j, isRVSet M S (RVFamily.graphPiece _ _ q i j)) (i j L' z) (hz : z ∈ RVFamily.graphPiece _ _ q i j) :=
    ((signedShear_reduct (J := J) v hv s hs G L' hO g P agrees units clamp powers).setInvariant S
      (fun t => signedShear_base v hv s hs G L' _ (base t).1) qe (defG i j) z).mpr hz
  have outside (V Y : Over (J := JS) A 1) (q : (sh V).Points ≃ (sh Y).Points)
      (defG : ∀ i j, isRVSet M S (RVFamily.graphPiece _ _ q i j)) (a : V.points A)
      (miss : ¬ ∃ b, WholeMatch (lab V) (lab Y) q a b) : Additive.ofMul ((pointTuple V a 0).2) ∈ G := by
    by_contra h
    apply miss
    apply independent_signed_match O hO v hv s hs G P S A defSharp V Y q (action V Y q defG) a
    exact linearIndependent_unique_iff.mpr (fun e => h ((Submodule.Quotient.mk_eq_zero G).mp e))
  let lang : ValueLanguage (J := JG) G :=
    ⟨definableFun_of_graph primitives.value_mul,fun e => definableFun_of_graph (primitives.value_power e)⟩
  have reverse : (fun b a => WholeMatch (lab U) (lab W) f a b) = WholeMatch (lab W) (lab U) f.symm :=
    funext fun b => funext fun a => propext (wholeMatch_inverse _ _ f a b).symm
  have tr {I : Type} [Finite I] (D : Set (I → RV0 O)) (hd : isRVSet M S D) :=
    residue_trace_definable O hO P S B (G : Set (Additive O.ValueGroupˣ)) T pow primitives g agrees clamp units hsec qe base D hd
  let μ := positiveUnitEuler O hO P S B @tr χ
  have chi := positiveUnitEuler_line O hO P S B @tr χ ray (positiveUnitLine_good O hO P S A defSharp he)
  apply conclude_unary_matching O hO G P S A defSharp @interpret (lang.avoidance sat) @witness he μ chi U W f graph
  · exact tagged_match_graph_definable (S := S) val A defSharp U W f graph reflect (signed_label_fiber_relation O hO P S 1)
  · rw [reverse]
    exact tagged_match_graph_definable (S := S) val A defSharp W U f.symm inv reflect (signed_label_fiber_relation O hO P S 1)
  · exact outside U W f graph
  · intro b missing
    exact outside W U f.symm inv b (fun ⟨a,h⟩ => missing ⟨a,(wholeMatch_inverse _ _ f a b).mp h⟩)

end GeneralizedEuler.Section4
