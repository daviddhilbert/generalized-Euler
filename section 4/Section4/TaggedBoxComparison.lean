module

public import Section4.ResidueProductBoxRanks
public import Section4.BoxPresentations
import all Section4.BoxPresentations
import all Section4.AlphabetRankProfiles
import all Section4.ValueScaleAlphabet
import all Section4.ValueEmbedding
import all Section4.SignedTensorFactors
import all Section4.ValueBoxProducts
import all Section4.QuotientSpanProfiles
import all Section4.UnaryTaggedComparison
import all Section4.BoxRanksFromLifts
public import Section4.ResidueProductProfiles
public import Section4.ResidueBaseValues
import all Section4.RVScissorRealization
import all Section4.TaggedLiftRealization
import all Section4.RVFamilyOperations
import all Section4.RVFamilySemiring
import all Section4.Objects
import all Section4.BoxScaleProfiles
import all Section4.Factors

/-! Recover the positive value class of a finite tagged box union from
its residue product and its two Euler characteristics. All scissor sums
are taken in the concrete value and RV semirings. -/
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


variable {C : Type*} [LinearOrder C] [BoundedOrder C] [Nontrivial C] [Fintype C]
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)]
  (B : PaddedBox.Alphabet G C) (L : PaddedBox.BoxLanguage (J := JG) G)
  (signedDef : ∀ {n} {D : Set (Fin n → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    A.Definable JS (mapTuples (positiveValueEmb O) '' D))
open PaddedBox
local notation "boxes" => taggedBoxes B L A (positiveValueEmb O) signedDef
local notation "lift" => valueFactorHom M S val A defSharp liftIso

omit [LinearOrder K] [IsStrictOrderedRing K] [Module F (Additive (PositiveRV O))] [Nontrivial C] [Fintype C] in
private theorem box_tags_unsigned {m k} (a : Fin m → Fin k → C) (i : Fin m) :
    unsignedPoint O A (boxes a) '' {p : (boxes a).points A | valuePointTag (boxes a) p = i} =
      {x | ∀ j, x j ∈ (side B.width (a i j)).domain} := by
  have same {x : Fin k → V} : x ∈ boxCarrier B (a i) ↔ ∀ j, x j ∈ (side B.width (a i j)).domain :=
    forall_congr' fun j => (side_domain B.width _ _).symm
  ext x
  constructor
  · rintro ⟨⟨t,p⟩,eq,rfl⟩
    obtain rfl : t=i := eq
    obtain ⟨z,hz,ez⟩ := p.property
    have ux : unsignedPoint O A (boxes a) ⟨t,p⟩ = z := by
      change (fun u : SignedValueGroup O => Additive.ofMul u.2) ∘ p.val = z
      rw [← ez]; rfl
    rw [ux]; exact same.mp hz
  · intro hx
    exact ⟨⟨i,mapTuples (positiveValueEmb O) x,⟨x,same.mpr hx,rfl⟩⟩,rfl,rfl⟩

include hv hs agrees units clamp powers in
theorem compare_tagged_box_products
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)),
      ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    (order : (G : Set V).Definable JG {x : Fin 2 → V | x 0 ≤ x 1})
    (step : V) (positive : 0 < step)
    (sat : ∀ fs : Finset V, UnaryValueSaturation JG (↑(G ⊔ Submodule.span F (fs : Set V)) : Set V))
    (k : ℕ) {m n} (a : Fin m → Fin (k+1) → C) (b : Fin n → Fin (k+1) → C)
    {l : ℕ} (R : RVObject M S l) (res : R.IsResidue M S val) (nonempty : R.carrier.Nonempty)
    (witness : ∀ {i} (D : Set (Fin i → RV0 O)), isRVSet M S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
    (eq : objectClass M S ⟨l,R⟩ * lift (taggedValueClass A (boxes a)) =
      objectClass M S ⟨l,R⟩ * lift (taggedValueClass A (boxes b)))
    (bounded geometric : SemiringOfSets (J := JS) A →+* ℤ)
    (bp : bounded ((embeddingMeasure (G : Set V) A (positiveValueEmb O) signedDef).descend (pieceClass _ L.point)) = 1)
    (br : bounded ((embeddingMeasure (G : Set V) A (positiveValueEmb O) signedDef).descend (pieceClass _ L.ray)) = 0)
    (gp : geometric ((embeddingMeasure (G : Set V) A (positiveValueEmb O) signedDef).descend (pieceClass _ L.point)) = 1)
    (gr : geometric ((embeddingMeasure (G : Set V) A (positiveValueEmb O) signedDef).descend (pieceClass _ L.ray)) = -1)
    (eb : bounded (taggedValueClass A (boxes a)) = bounded (taggedValueClass A (boxes b)))
    (eg : geometric (taggedValueClass A (boxes a)) = geometric (taggedValueClass A (boxes b))) :
    taggedValueClass A (boxes a) = taggedValueClass A (boxes b) := by
  let τ := cutoff B.width
  have old (c : C) : τ c ∈ G := by unfold τ cutoff; split; exact G.zero_mem; exact B.old c
  have nn (c : C) : 0 ≤ τ c := by
    unfold τ cutoff; split
    · rfl
    · rename_i h; exact (B.positive c (fun e => h (.inl e)) (fun e => h (.inr e))).le
  have d (c : C) : (G : Set V).Definable JG {x : Unit → V | x () ∈ (side B.width c).domain} := by
    have src := (scalePiece_definable G B.width B.old L.intervals L.point L.ray c).preimage_comp (fun _ : Fin 1 => ())
    convert src using 1; ext x; exact side_domain B.width c (x ())
  have pos (c : C) (v : V) (h : side B.width c = .bounded v) : 0 < v := by
    unfold side at h
    split at h; contradiction
    split at h; contradiction
    rename_i lo hi
    exact (BoxSide.bounded.inj h) ▸ B.positive c lo hi
  have max := maximal_box_vectors_of_residue_product_equality O v hv s hs G hO P g agrees units clamp powers
    S A defSharp liftIso base qe (boxes a) (boxes b) R res nonempty witness eq τ old nn order step positive sat
    (fun i => side B.width ∘ a i) (fun i => side B.width ∘ b i)
    (fun i j => d (a i j)) (fun i j => d (b i j)) (fun i j => pos (a i j)) (fun i j => pos (b i j))
    (box_tags_unsigned O G A B L signedDef a) (box_tags_unsigned O G A B L signedDef b)
  rw [taggedBoxes_class,taggedBoxes_class] at eb eg ⊢
  apply congrArg _
  let σ := (embeddingMeasure (G : Set V) A (positiveValueEmb O) signedDef).descend
  exact unionValue_eq_of_counts B L k a b max (bounded.comp σ) (geometric.comp σ) bp br gp gr eb eg

end GeneralizedEuler.Section4
