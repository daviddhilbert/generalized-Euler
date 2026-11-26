module

public import Section4.SignedRectangleFactors
public import Section4.RectangleRange
import all Section4.RectangleMap
import all Section4.RectangleClasses
import all Section4.PositivePresentations
import all Section4.ValuePullback
import all Section4.Scissors
import all Section4.Objects

/-! Surjectivity in Proposition 4.21 over the fixed base, using the value
interpretation, Lemma 4.12, saturation and the canonical RV reduct. -/
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
local instance canonicalAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) :=
  inferInstanceAs (JG.Structure O.ValueGroupˣ)

variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp _ (signedLabel O hO) D))
  (liftIso : ∀ {k} (D C : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS C →
    ∀ e : D ≃ C, A.Definable JS {w : Fin k ⊕ Fin k → SignedValueGroup O |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp _ (signedLabel O hO) D) (sharp _ (signedLabel O hO) C))
  (signedDef : ∀ {n} {D : Set (Fin n → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    A.Definable JS ((fun γ => positiveValueLabel O ∘ γ) '' D))
  (e : Fin 1 → SignedValueGroup O) (he : A.Definable JS ({e} : Set (Fin 1 → SignedValueGroup O)))

include g agrees units clamp powers hv hs signedDef in
theorem canonical_rectangle_surjective
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
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) :
    Function.Surjective (balancedRectangleMap _ S (signedLabel O hO) A defSharp liftIso e he) := by
  classical
  let M := canonicalStructure (L := J) O hO P
  let line := residueClass (sharpObject M S (signedLabel O hO) {e} (defSharp he))
    (sharp_residue M S (signedLabel O hO) A defSharp {e} (Set.finite_singleton _) he)
  let := (Polynomial.eval₂RingHom (Nat.castRingHom _) line).toAlgebra
  let := (Polynomial.eval₂RingHom (Nat.castRingHom _) (pieceClass {e} he)).toAlgebra
  let tensor := TensorProduct (Polynomial ℕ) (ResidueSemiring M S (signedLabel O hO)) (SemiringOfSets (J := JS) A)
  let f : tensor →+* RVSemiring M S := balancedRectangleMap M S (signedLabel O hO) A defSharp liftIso e he
  have lang : ValueLanguage (J := JG) G :=
    ⟨definableFun_of_graph primitives.value_mul,fun t => definableFun_of_graph (primitives.value_power t)⟩
  have pull {n} {D : Set (Fin n → Additive O.ValueGroupˣ)} (hd : (G : Set _).Definable JG D) :
      isRVSet M S (positiveSharp O v D) := by
    rw [← signed_sharp_positive (J := J) O hO v hv P D]
    exact defSharp (signedDef hd)
  change Function.Surjective f
  refine generators_in_range (M := M) (S := S) (T := tensor) f ?_
  rintro ⟨n,U⟩
  obtain ⟨N,D,hD,pos,eq⟩ := positive_object_classes O hO P S U minus rvSat
  rw [eq]
  apply f.rangeS.sum_mem
  intro i _
  apply f.rangeS.sum_mem
  intro b _
  obtain ⟨l,p,_,_,supports,charts⟩ := canonical_rectangles v hv s hs G B hO P g agrees units clamp powers
    primitives S base qe sat (D i b) (hD i b)
  obtain ⟨R,hr,pr,eqR,eqU⟩ := positive_partition_class O v s hs hO P powers S reps lang @pull
    (D i b) (hD i b) (pos i b) p supports charts
  rw [eqU]
  apply f.rangeS.sum_mem
  intro j _
  obtain ⟨idx,eq⟩ := eqR j
  let res := positiveObject O hO P S (R j) (hr j) (pr j)
  have hres : res.IsResidue M S (signedLabel O hO) := by
    have h := coded_residue_object O hO v hv P S (p j).value.frame idx (p j).residues (eq ▸ hr j)
    change (Set.range (fun x : R j => signedLabel O hO ∘ x.val)).Finite
    rw [eq]; exact h
  let d := (p j).value.domain
  let sd := (fun γ => positiveValueLabel O ∘ γ) '' d
  have hsd := signedDef (p j).value.definable
  have term := product_in_rectangle_range M S (signedLabel O hO) A defSharp liftIso e he
    res hres sd hsd
  have iso : (sharpObject M S (signedLabel O hO) sd (defSharp hsd)).Isomorphic M S
      (positiveObject O hO P S (positiveSharp O v d) (pull (p j).value.definable) (positiveSharp_pos O v d)) := by
    change RVDefinablyEquivalent M S.carrier (sharp M (signedLabel O hO) sd) (positiveSharp O v d)
    rw [signed_sharp_positive (J := J) O hO v hv P d]
    exact ⟨Equiv.refl _,definable_identity_label M S (pull (p j).value.definable)⟩
  have same : objectClass M S ⟨_,sharpObject M S (signedLabel O hO) sd (defSharp hsd)⟩ =
      objectClass M S ⟨_,positiveObject O hO P S (positiveSharp O v d) (pull (p j).value.definable) (positiveSharp_pos O v d)⟩ :=
    scissors_sound M S (RVRelation.iso _ _ iso)
  rw [same] at term
  exact term

end GeneralizedEuler.Section4
