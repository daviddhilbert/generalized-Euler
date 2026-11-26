module

public import Section4.BoundedValueBoxes
public import Section4.LiftQuotientProfiles
public import Section4.SignedTensorFactors
import all Section4.SignedTensorFactors
import all Section4.SignedRectangleFactors
import all Section4.BoundedValueBoxes
import all Section4.QuotientSpanProfiles
import all Section4.SignedValueGeneration
import all Section4.ValueEmbedding
import all Section4.ValueScissors
import all Section4.UnaryTaggedComparison
import all Section4.Factors
import all Section4.TaggedLiftRealization
import all Section4.RVTaggedEquivalence

/-! Products of bounded open positive RV annuli are definably bijective
precisely when their interval widths can be paired by scale. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject Set
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

variable [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F (Additive O.ValueGroupˣ)]
local notation "V" => Additive O.ValueGroupˣ


local notation "embed" => mapTuples (positiveValueEmb O)
variable {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem unsigned_embedded_range {n} (D : Set (Fin n → V))
    (hD : A.Definable JS (embed '' D)) :
    range (unsignedPoint O A (single _ hD)) = D := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨y,hy,ey⟩ : x.2.val ∈ embed '' D := x.2.property
    change (fun u : SignedValueGroup O => Additive.ofMul u.2) ∘ x.2.val ∈ D
    rw [← ey]; exact hy
  · intro h
    let p : (single _ hD).points A := ⟨0,embed z,⟨z,h,rfl⟩⟩
    exact ⟨p,rfl⟩

include hv hs agrees units clamp powers defSharp liftIso in
theorem bounded_rv_annuli_iff_same_scales
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)),
      ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    (signedDef : ∀ {n} {D : Set (Fin n → V)}, (G : Set V).Definable JG D → A.Definable JS (embed '' D))
    (lang : ValueLanguage (J := JG) G)
    (order : (G : Set V).Definable JG {x : Fin 2 → V | x 0 ≤ x 1})
    (leDef : ∀ t ∈ G, (G : Set V).Definable JG {x : Unit → V | x () ≤ t})
    (step : V) (pos : 0 < step)
    (sat : ∀ fs : Finset V, UnaryValueSaturation JG (↑(G ⊔ Submodule.span F (fs : Set V)) : Set V))
    {m n : ℕ} (a : Fin m → V) (b : Fin n → V)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (ba : ∀ i, a i ∈ G) (bb : ∀ j, b j ∈ G)
    (da : ∀ i, (G : Set V).Definable JG {x : Unit → V | x () ∈ Ioo 0 (a i)})
    (db : ∀ i, (G : Set V).Definable JG {x : Unit → V | x () ∈ Ioo 0 (b i)}) :
    RVDefinablyEquivalent M S.carrier (positiveSharp O v (boundedBox a)) (positiveSharp O v (boundedBox b)) ↔
    ∃ e : Fin m ≃ Fin n, ∀ i, scaleSpace F (a i) = scaleSpace F (b (e i)) := by
  have defA := boundedBox_definable G a da
  have defB := boundedBox_definable G b db
  let U := single _ (signedDef defA)
  let W := single _ (signedDef defB)
  have leftEq : sharp M val (embed '' boundedBox a) = positiveSharp O v (boundedBox a) :=
    signed_sharp_positive O hO v hv P _
  have rightEq : sharp M val (embed '' boundedBox b) = positiveSharp O v (boundedBox b) :=
    signed_sharp_positive O hO v hv P _
  rw [← leftEq,← rightEq]
  constructor
  · intro iso
    have tagged : (sh U).Iso (sh W) := RVFamily.iso_retag _ _ (Equiv.refl (Fin 1)) (fun _ => iso)
    apply bounded_widths_of_rank_sets G a b ha hb ba bb step pos order da db sat
    intro c _ _
    let H (_ : Unit) := G ⊔ scaleSpace F c
    have eq := quotient_profiles_of_lift_iso O v hv s hs G hO P g agrees units clamp powers
      S A defSharp base qe U W tagged H (fun _ => le_sup_left)
    let rank (p : (i : Unit) → Submodule F (V ⧸ H i)) := Module.finrank F (p ())
    have same := congrArg (fun data => rank '' data) eq
    change (fun x => Module.finrank F (quotientTupleSpan (H ()) x)) '' boundedBox a =
      (fun x => Module.finrank F (quotientTupleSpan (H ()) x)) '' boundedBox b
    rw [← unsigned_embedded_range O A _ (signedDef defA),← unsigned_embedded_range O A _ (signedDef defB),
      ← Set.range_comp,← Set.range_comp]
    simpa only [← Set.range_comp,Function.comp_def,rank,U,W] using same
  · rintro ⟨e,scales⟩
    have arity : m=n := by simpa using Fintype.card_congr e
    subst n
    obtain ⟨f,hf⟩ := paired_widths_box_bijection G a b ha hb ba bb lang leDef defA e scales
    obtain ⟨f',hf'⟩ := embedded_value_bijection (G : Set V) A (positiveValueEmb O) @signedDef _ _ f hf
    exact liftIso _ _ (signedDef defA) (signedDef defB) f' hf'

end GeneralizedEuler.Section4
