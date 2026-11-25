module

public import Section2.DefinableResidueCharts
public import Mathlib.ModelTheory.Definability

/-! Transport of definable bijections to the residue field in Theorem 2.31. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

variable {K : Type z} [Field K] (O : ValuationSubring K) {I J : Type}

def embedResidueCoordinates (x : I → Residue O) : I → RV0 O := residueRV O ∘ x

theorem embedResidueCoordinates_injective :
    Function.Injective (embedResidueCoordinates O (I := I)) :=
  fun _ _ h => funext fun i => residueRV_injective O (congrFun h i)

def embeddedResidueSet (D : Set (I → Residue O)) : Set (I → RV0 O) :=
  Set.range (fun x : D => embedResidueCoordinates O x.val)

def equivEmbeddedResidueSet (D : Set (I → Residue O)) : D ≃ embeddedResidueSet O D :=
  Equiv.ofInjective _ (fun _ _ h => Subtype.ext (embedResidueCoordinates_injective O h))

@[simp] theorem equivEmbeddedResidueSet_val (D : Set (I → Residue O)) (x : D) :
    (equivEmbeddedResidueSet O D x).val = embedResidueCoordinates O x.val := by rfl

def residueGraph {D : Set (I → Residue O)} (f : D → J → Residue O) : Set (I ⊕ J → Residue O) :=
  {x | ∃ d : D, d.val = x ∘ Sum.inl ∧ f d = x ∘ Sum.inr}

variable {L : Language.{u, v}} [L.Structure (Residue O)]

/-- Definable equivalence within the ordinary residue-field language. -/
def ResidueDefinablyEquivalent (D : Set (I → Residue O)) (B : Set (J → Residue O)) : Prop :=
  ∃ e : D ≃ B, (Set.univ : Set (Residue O)).Definable L (residueGraph O (fun x => (e x).val))

variable {E : Type w} (M : SortedStructure L E (CanonicalSort O))

/-- The induced residue structure from van den Dries (1997), Theorem A.
The statement uses all parameters as in Convention 2.1. -/
def HasInducedResidueDefinability : Prop :=
  ∀ {H : Type} [Finite H] (D : Set (H → Residue O)),
    (Set.univ : Set (Residue O)).Definable L D ↔
      SortedDefinableOver M (fun _ => Set.univ)
        {a : ∀ s, RVVariables H s → CanonicalSort O s | a .rv ∈ embeddedResidueSet O D}

private theorem embedded_residueGraph {D : Set (I → Residue O)} {B : Set (J → Residue O)}
    (e : D ≃ B) (f : embeddedResidueSet O D ≃ embeddedResidueSet O B)
    (hf : ∀ x, f (equivEmbeddedResidueSet O D x) = equivEmbeddedResidueSet O B (e x)) :
    rvGraph (X := CanonicalSort O) (fun x => (f x).val) =
      {a : ∀ s, RVVariables (I ⊕ J) s → CanonicalSort O s |
        a .rv ∈ embeddedResidueSet O (residueGraph O (fun x => (e x).val))} := by
  ext a
  constructor
  · rintro ⟨x, hx, hfx⟩
    let y := (equivEmbeddedResidueSet O D).symm x
    have hy : equivEmbeddedResidueSet O D y = x := (equivEmbeddedResidueSet O D).apply_symm_apply x
    have hfy : equivEmbeddedResidueSet O B (e y) = f x := (hf y).symm.trans (congrArg f hy)
    let v : I ⊕ J → Residue O := Sum.elim y.val (e y).val
    refine ⟨⟨v, ⟨y, rfl, rfl⟩⟩, ?_⟩
    funext i
    rcases i with i | i
    · exact congrFun ((congrArg Subtype.val hy).trans hx) i
    · exact congrFun ((congrArg Subtype.val hfy).trans hfx) i
  · rintro ⟨v, hv⟩
    obtain ⟨y, hy, hye⟩ := v.property
    refine ⟨equivEmbeddedResidueSet O D y, ?_, ?_⟩
    · funext i
      rw [equivEmbeddedResidueSet_val, hy]
      exact congrFun hv (.inl i)
    · change (f (equivEmbeddedResidueSet O D y)).val = a .rv ∘ Sum.inr
      rw [hf y, equivEmbeddedResidueSet_val]
      rw [show (e y).val = v.val ∘ Sum.inr from hye]
      funext i
      exact congrFun hv (.inr i)

/-- A bijection of two embedded residue sets is definable precisely when
the corresponding internal residue-field bijection is definable. -/
theorem rvDefinablyEquivalent_iff_residue [Finite I] [Finite J]
    (hA : HasInducedResidueDefinability O M) (D : Set (I → Residue O)) (B : Set (J → Residue O)) :
    RVDefinablyEquivalent M (fun _ => Set.univ) (embeddedResidueSet O D) (embeddedResidueSet O B) ↔
      ResidueDefinablyEquivalent (L := L) O D B := by
  constructor
  · rintro ⟨f, hf⟩
    let e := (equivEmbeddedResidueSet O D).trans (f.trans (equivEmbeddedResidueSet O B).symm)
    have hcom (x : D) : f (equivEmbeddedResidueSet O D x) = equivEmbeddedResidueSet O B (e x) :=
      ((equivEmbeddedResidueSet O B).apply_symm_apply _).symm
    rw [embedded_residueGraph O e f hcom] at hf
    exact ⟨e, (hA _).mpr hf⟩
  · rintro ⟨e, he⟩
    let f := (equivEmbeddedResidueSet O D).symm.trans (e.trans (equivEmbeddedResidueSet O B))
    have hcom (x : D) : f (equivEmbeddedResidueSet O D x) = equivEmbeddedResidueSet O B (e x) :=
      congrArg (fun y => equivEmbeddedResidueSet O B (e y)) ((equivEmbeddedResidueSet O D).symm_apply_apply x)
    refine ⟨f, ?_⟩
    rw [embedded_residueGraph O e f hcom]
    exact (hA _).mp he

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)

/-- A finite-valued definable RV set admits a residue-field normal form
that is definable in the residue field's own language. -/
theorem exists_internal_residue_normalization {n : ℕ} (D : Set (Fin n → RV0 O))
    [Finite (Set.range (fun x : D => unsignedValue O ∘ x.val))]
    (hA : HasInducedResidueDefinability O (canonicalStructure (L := L) O hO power))
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      {a : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | a .rv ∈ D}) :
    ∃ R : Set ((Fin n ⊕ Unit) → Residue O), (Set.univ : Set (Residue O)).Definable L R ∧
      RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
        D (embeddedResidueSet O R) := by
  obtain ⟨B, e, he, hB, hvalues⟩ := exists_definable_equiv_to_residue_tuples (L := L) O hO power D hD
  let R := embedResidueCoordinates O ⁻¹' B
  have hset : embeddedResidueSet O R = B := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      exact r.property
    · intro hx
      have heq : embedResidueCoordinates O (rvResidue O ∘ x) = x := funext fun i =>
        residueRV_rvResidue_of_mem_range O (hvalues ⟨x, hx⟩ i)
      have hr : rvResidue O ∘ x ∈ R := by
        change embedResidueCoordinates O (rvResidue O ∘ x) ∈ B
        rwa [heq]
      exact ⟨⟨rvResidue O ∘ x, hr⟩, heq⟩
  refine ⟨R, (hA R).mpr ?_, ?_⟩
  · rwa [hset]
  · rw [hset]
    exact ⟨e, he⟩

/-- The transport in Theorem 2.31. The classification premise is the
dimension and Euler-characteristic criterion from van den Dries's book,
applied to the two definable residue normal forms. -/
theorem rvDefinablyEquivalent_iff_of_residue_classification
    {n m : ℕ} (U : Set (Fin n → RV0 O)) (V : Set (Fin m → RV0 O))
    (R : Set ((Fin n ⊕ Unit) → Residue O)) (S : Set ((Fin m ⊕ Unit) → Residue O))
    (hA : HasInducedResidueDefinability O (canonicalStructure (L := L) O hO power))
    (hU : RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      U (embeddedResidueSet O R))
    (hV : RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) (fun _ => Set.univ)
      V (embeddedResidueSet O S))
    (dimU dimV : ℕ) (chiU chiV : ℤ)
    (classification : ResidueDefinablyEquivalent (L := L) O R S ↔ dimU = dimV ∧ chiU = chiV) :
    RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) (fun _ => Set.univ) U V
      ↔ dimU = dimV ∧ chiU = chiV :=
  (RVDefinablyEquivalent.iff_of_normalizations hU hV).trans
    ((rvDefinablyEquivalent_iff_residue O _ hA R S).trans classification)

end GeneralizedEuler.Section2
