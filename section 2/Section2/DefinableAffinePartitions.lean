module

public import Section2.AffineRVEquivalence

/-! Fixed-base assembly of the affine value pieces of Lemma 2.29. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder RVValueSection

universe u v w z

variable {E : Type w} [Field E]

/-- An affine value graph in the coordinate order of the original set. -/
@[expose]
def reindexedAffineValueGraph {V : Type*} [AddCommGroup V] [Module E V]
    {I : Type} {n m : ℕ} (coords : Fin m ⊕ Fin n ≃ I)
    (D : Set (Fin m → V)) (coeff : Fin n → Fin m → E) (δ : Fin n → V) :
    Set (I → V) :=
  {x | x ∘ coords ∘ Sum.inl ∈ D ∧
    ∀ i, x (coords (.inr i)) = affineCoordinates coeff δ (x ∘ coords ∘ Sum.inl) i}

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)

/-- The positive part of the pullback of an unsigned value set. -/
@[expose]
def positiveValuePullback {I : Type} (D : Set (I → Additive (O.ValueGroupˣ))) : Set (I → RV0 O) :=
  {x | (∀ i, IsPositiveRV O (x i)) ∧ (Additive.ofMul ∘ valueCoordinate ∘ x) ∈ D}

variable {g : E → PositiveField K →* PositiveField K}
  {P : E → RV0 O → RV0 O} (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

set_option linter.style.haveILetI false in
theorem positiveValuePullback_reindexedAffineValueGraph {I : Type} {m n : ℕ}
    (coords : Fin m ⊕ Fin n ≃ I) (D : Set (Fin m → Additive O.ValueGroupˣ))
    (coeff : Fin n → Fin m → E) (δ : Fin n → Additive O.ValueGroupˣ)
    (u : Fin n → RV0 O) (hu : ∀ i, IsPositiveRV O (u i))
    (hδ : ∀ i, Additive.ofMul (valueCoordinate (u i)) = δ i) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    positiveValuePullback O (reindexedAffineValueGraph coords D coeff δ) =
      affineRVSource O P coords coeff u (positiveValuePullback O D) := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  ext x
  let t := x ∘ coords ∘ Sum.inl
  let f := Additive.ofMul ∘ valueCoordinate ∘ t
  let lift := rvAffineMonomial O P coeff u t
  have hval (hx : ∀ j, IsPositiveRV O (x j)) (i : Fin n) :
      Additive.ofMul (valueCoordinate (lift i)) = affineCoordinates coeff δ f i := by
    have h := (positive_affine_monomial O hP hzero hone hadd hmul hunit coeff u hu t
      (fun j => hx (coords (.inl j))) i).2
    have hd : Additive.ofMul ∘ valueCoordinate ∘ u = δ := funext hδ
    simpa only [lift, rvAffineMonomial, hd, f] using h
  change ((∀ j, IsPositiveRV O (x j)) ∧ f ∈ D ∧
      ∀ i, Additive.ofMul (valueCoordinate (x (coords (.inr i)))) = affineCoordinates coeff δ f i) ↔
    ((∀ j, IsPositiveRV O (x j)) ∧ ((∀ j, IsPositiveRV O (t j)) ∧ f ∈ D) ∧
      ∀ i, valueCoordinate (x (coords (.inr i))) = valueCoordinate (lift i))
  constructor
  · rintro ⟨hx, ht, he⟩
    exact ⟨hx, ⟨fun j => hx (coords (.inl j)), ht⟩,
      fun i => Additive.ofMul.injective ((he i).trans (hval hx i).symm)⟩
  · rintro ⟨hx, ⟨_, ht⟩, he⟩
    exact ⟨hx, ht, fun i => (congrArg Additive.ofMul (he i)).trans (hval hx i)⟩

set_option linter.style.haveILetI false in
/-- Once the fixed-base affine pieces have been chosen in the value
language, their RV pullbacks trivialize over the original parameters.
The intercepts use the base-compatible positive section. -/
theorem definable_affine_partition_pullback
    {L : Language.{u, v}} [L.Structure K] [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (A : ∀ s, Set (CanonicalSort O s)) (S : RVValueSection O)
    {I : Type} {m n l : ℕ} (coords : Fin l → (Fin m ⊕ Fin n ≃ I))
    (D : Fin l → Set (Fin m → Additive O.ValueGroupˣ))
    (coeff : Fin l → Fin n → Fin m → E) (δ : Fin l → Fin n → Additive O.ValueGroupˣ)
    (hδ : ∀ j i, S.representative (δ j i).toMul ∈ A .rv)
    (U : Set (I → Additive O.ValueGroupˣ)) (tag : Fin l ↪ RV0 O)
    (htag : ∀ j, tag j ∈ A .rv) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    let pieces := fun j => reindexedAffineValueGraph (coords j) (D j) (coeff j) (δ j)
    U = ⋃ j, pieces j →
    Pairwise (fun i j => Disjoint (pieces i) (pieces j)) →
    (∀ j, SortedDefinableOver (canonicalStructure (L := L) O hO P) A
      {x : ∀ s, RVVariables I s → CanonicalSort O s | x .rv ∈ positiveValuePullback O (pieces j)}) →
    RVDefinablyEquivalent (canonicalStructure (L := L) O hO P) A
      (positiveValuePullback O U)
      (taggedRVUnion (fun j => affineRVTarget O (n := n) (positiveValuePullback O (D j))) tag) := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  let pieces (j : Fin l) := reindexedAffineValueGraph (coords j) (D j) (coeff j) (δ j)
  dsimp only
  intro hU hdisj hdef
  let X (j : Fin l) := positiveValuePullback O (pieces j)
  let Y (j : Fin l) := affineRVTarget O (n := n) (positiveValuePullback O (D j))
  let u (j : Fin l) (i : Fin n) := S.representative (δ j i).toMul
  have hupos (j : Fin l) (i : Fin n) : IsPositiveRV O (u j i) := S.representative_pos _
  have huval (j : Fin l) (i : Fin n) : Additive.ofMul (valueCoordinate (u j i)) = δ j i := by
    apply Additive.toMul.injective
    apply Units.ext
    change (valueCoordinate (S.representative (δ j i).toMul) : O.ValueGroup) = (δ j i).toMul
    rw [coe_valueCoordinate (S.representative_ne_zero (δ j i).toMul)]
    exact S.unsignedValue_representative (δ j i).toMul
  have hcharts (j : Fin l) :
      RVDefinablyEquivalent (canonicalStructure (L := L) O hO P) A (X j) (Y j) := by
    have hx : X j = affineRVSource O P (coords j) (coeff j) (u j) (positiveValuePullback O (D j)) :=
      positiveValuePullback_reindexedAffineValueGraph O hP hzero hone hadd hmul hunit
        (coords j) (D j) (coeff j) (δ j) (u j) (hupos j) (huval j)
    rw [hx]
    apply affineRVChart_definablyEquivalent O P (coords j) (coeff j) (u j) _ hO A (hδ j)
    · intro t ht i
      exact (positive_affine_monomial O hP hzero hone hadd hmul hunit
        (coeff j) (u j) (hupos j) t ht i).1
    · rw [← hx]
      exact hdef j
  have hdisj' : Pairwise (fun i j => Disjoint (X i) (X j)) :=
    fun _ _ hij => Set.disjoint_left.mpr (fun _ hx hy =>
      Set.disjoint_left.mp (hdisj hij) hx.2 hy.2)
  have hwhole : positiveValuePullback O U = ⋃ j, X j := by
    ext x
    constructor
    · intro hx
      have hv := hx.2
      rw [hU, Set.mem_iUnion] at hv
      obtain ⟨j, hj⟩ := hv
      exact Set.mem_iUnion.mpr ⟨j, hx.1, hj⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact ⟨hj.1, hU.symm ▸ Set.mem_iUnion.mpr ⟨j, hj.2⟩⟩
  rw [hwhole]
  exact rvDefinablyEquivalent_tagged_union (M := canonicalStructure (L := L) O hO P)
    (A := A) X Y tag htag hdisj' hcharts

end GeneralizedEuler.Section2
