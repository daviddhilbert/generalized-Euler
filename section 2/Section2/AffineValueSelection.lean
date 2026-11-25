module

public import Section2.DefinableAffinePartitions
public import Mathlib.Data.Fintype.CardEmbedding

/-! Selecting and flattening a fixed-base affine partition from
coordinate charts and the cited piecewise-affine theorem. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

/-- A projection onto at most k coordinates can be enlarged to k
coordinates and completed to a coordinate order. -/
theorem exists_coordinate_order_extending {I : Type} [Fintype I] {r k : ℕ}
    (e : Fin r ↪ I) (hr : r ≤ k) (hk : k ≤ Fintype.card I) :
    ∃ c : Fin k ⊕ Fin (Fintype.card I - k) ≃ I,
      Set.range e ⊆ Set.range (c ∘ Sum.inl) := by
  classical
  let image := (Finset.univ : Finset (Fin r)).map e
  have hcard : image.card ≤ k := by simpa [image] using hr
  obtain ⟨s, hs, hsk⟩ := Finset.exists_superset_card_eq hcard hk
  let T : Set I := s
  have hsT : Fintype.card T = k := by simpa [T] using hsk
  have hnotT : Fintype.card (Tᶜ : Set I) = Fintype.card I - k := by
    rw [Fintype.card_compl_set, hsT]
  let l := (Fintype.equivFinOfCardEq hsT).symm
  let r := (Fintype.equivFinOfCardEq hnotT).symm
  let c := (Equiv.sumCongr l r).trans (Equiv.Set.sumCompl T)
  refine ⟨c, ?_⟩
  rintro _ ⟨i, rfl⟩
  have h : e i ∈ T := hs (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  exact ⟨l.symm ⟨e i, h⟩, by simp [c]⟩

variable {E : Type w} [Field E] {V : Type z} [AddCommGroup V] [Module E V]
  {J : Language.{u, v}} [J.Structure V] {I : Type}

/-- The affine pieces and all their definability data over a specified
value subspace. This data can be passed directly to the RV pullback. -/
structure FixedBaseAffinePartition (W : Submodule E V) (U : Set (I → V)) (m n : ℕ) where
  count : ℕ
  coordinates : Fin count → (Fin m ⊕ Fin n ≃ I)
  domain : Fin count → Set (Fin m → V)
  coefficients : Fin count → Fin n → Fin m → E
  translation : Fin count → Fin n → V
  translation_mem : ∀ j i, translation j i ∈ W
  cover : U = ⋃ j, reindexedAffineValueGraph (coordinates j) (domain j) (coefficients j) (translation j)
  disjoint : Pairwise (fun i j =>
    Disjoint (reindexedAffineValueGraph (coordinates i) (domain i) (coefficients i) (translation i))
      (reindexedAffineValueGraph (coordinates j) (domain j) (coefficients j) (translation j)))
  domainDefinable : ∀ j, (W : Set V).Definable J (domain j)
  pieceDefinable : ∀ j, (W : Set V).Definable J
    (reindexedAffineValueGraph (coordinates j) (domain j) (coefficients j) (translation j))

/-- Theorem B in the graph form used here. The input is a definable
partial function and the output is a definable piecewise-affine
description over the same vector subspace. -/
def HasFixedBaseAffineGraphDecomposition (W : Submodule E V) (m n : ℕ) : Prop :=
  ∀ S : Set (Fin m ⊕ Fin n → V), (W : Set V).Definable J S →
    Set.InjOn (fun x => x ∘ Sum.inl) S →
    ∃ (l : ℕ) (D : Fin l → Set (Fin m → V)) (c : Fin l → Fin n → Fin m → E)
      (δ : Fin l → Fin n → V),
      (∀ j i, δ j i ∈ W) ∧
      S = ⋃ j, reindexedAffineValueGraph (Equiv.refl _) (D j) (c j) (δ j) ∧
      Pairwise (fun i j => Disjoint
        (reindexedAffineValueGraph (Equiv.refl _) (D i) (c i) (δ i))
        (reindexedAffineValueGraph (Equiv.refl _) (D j) (c j) (δ j))) ∧
      (∀ j, (W : Set V).Definable J (D j)) ∧
      ∀ j, (W : Set V).Definable J (reindexedAffineValueGraph (Equiv.refl _) (D j) (c j) (δ j))

/-- Starting with a definable coordinate-chart partition of the value
set, apply the affine graph theorem and combine the refined pieces.
Charts of lower dimension are padded using existing coordinates. -/
theorem exists_fixedBaseAffinePartition [Fintype I]
    (W : Submodule E V) (U : Set (I → V)) {m l : ℕ} (hm : m ≤ Fintype.card I)
    (C : Fin l → Set (I → V)) (hC : ∀ j, (W : Set V).Definable J (C j))
    (hcover : U = ⋃ j, C j) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (size : Fin l → ℕ) (hsize : ∀ j, size j ≤ m) (projection : ∀ j, Fin (size j) ↪ I)
    (hinj : ∀ j, Set.InjOn (fun x => x ∘ projection j) (C j))
    (haffine : HasFixedBaseAffineGraphDecomposition (J := J) W m (Fintype.card I - m)) :
    Nonempty (FixedBaseAffinePartition (J := J) W U m (Fintype.card I - m)) := by
  classical
  let n := Fintype.card I - m
  choose coords hcoords using fun j => exists_coordinate_order_extending (projection j) (hsize j) hm
  let C' (j : Fin l) : Set (Fin m ⊕ Fin n → V) :=
    (fun x => x ∘ (coords j).symm) ⁻¹' C j
  have hC' (j : Fin l) : (W : Set V).Definable J (C' j) := (hC j).preimage_comp (coords j).symm
  have hinj' (j : Fin l) : Set.InjOn (fun x => x ∘ Sum.inl) (C' j) := by
    intro x hx y hy hxy
    have hproj : (x ∘ (coords j).symm) ∘ projection j = (y ∘ (coords j).symm) ∘ projection j := by
      funext i
      obtain ⟨a, ha⟩ := hcoords j (Set.mem_range_self i)
      have he : (coords j).symm (projection j i) = .inl a := (coords j).symm_apply_eq.mpr ha.symm
      change x ((coords j).symm (projection j i)) = y ((coords j).symm (projection j i))
      rw [he]
      exact congrFun hxy a
    have h := hinj j hx hy hproj
    funext i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun h (coords j i)
  choose count D coeff δ hδ hlocal hlocalDisj hD hLocalDef using fun j =>
    haffine (C' j) (hC' j) (hinj' j)
  let Index := Σ j, Fin (count j)
  let := Fintype.ofFinite Index
  let enum := Fintype.equivFin Index
  let X (p : Index) := reindexedAffineValueGraph (coords p.1) (D p.1 p.2) (coeff p.1 p.2) (δ p.1 p.2)
  have hpiece (j : Fin l) (i : Fin (count j)) (x : I → V) :
      x ∈ X ⟨j, i⟩ ↔ x ∘ coords j ∈
        reindexedAffineValueGraph (Equiv.refl _) (D j i) (coeff j i) (δ j i) := Iff.rfl
  have back (j : Fin l) (x : I → V) : x ∘ coords j ∈ C' j ↔ x ∈ C j := by
    change (x ∘ coords j) ∘ (coords j).symm ∈ C j ↔ _
    have e : (x ∘ coords j) ∘ (coords j).symm = x := by
      funext i
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [e]
  have hpSub (p : Index) : X p ⊆ C p.1 := by
    intro x hx
    apply (back p.1 x).mp
    rw [hlocal p.1]
    exact Set.mem_iUnion.mpr ⟨p.2, (hpiece p.1 p.2 x).mp hx⟩
  have hdisj' : Pairwise (fun p q : Index => Disjoint (X p) (X q)) := by
    rintro ⟨i, j⟩ ⟨a, b⟩ hne
    by_cases he : i = a
    · subst a
      have hjb : j ≠ b := fun h => hne (congrArg (Sigma.mk i) h)
      exact Set.disjoint_left.mpr (fun x hx hy => Set.disjoint_left.mp (hlocalDisj i hjb)
        ((hpiece i j x).mp hx) ((hpiece i b x).mp hy))
    · exact Set.disjoint_left.mpr (fun _ hx hy => Set.disjoint_left.mp (hdisj he)
        (hpSub ⟨i, j⟩ hx) (hpSub ⟨a, b⟩ hy))
  refine ⟨⟨Fintype.card Index, fun i => coords (enum.symm i).1,
    fun i => D (enum.symm i).1 (enum.symm i).2,
    fun i => coeff (enum.symm i).1 (enum.symm i).2,
    fun i => δ (enum.symm i).1 (enum.symm i).2,
    fun i => hδ (enum.symm i).1 (enum.symm i).2, ?_, ?_,
    fun i => hD (enum.symm i).1 (enum.symm i).2, ?_⟩⟩
  · ext x
    constructor
    · intro hx
      rw [hcover, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      have hx' : x ∘ coords j ∈ C' j := (back j x).mpr hj
      rw [hlocal j, Set.mem_iUnion] at hx'
      obtain ⟨i, hi⟩ := hx'
      apply Set.mem_iUnion.mpr
      refine ⟨enum ⟨j, i⟩, ?_⟩
      change x ∈ X (enum.symm (enum ⟨j, i⟩))
      rw [Equiv.symm_apply_apply]
      exact (hpiece j i x).mpr hi
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨(enum.symm i).1, hpSub (enum.symm i) hi⟩
  · intro i j hij
    exact hdisj' (fun h => hij (enum.symm.injective h))
  · intro i
    exact (hLocalDef (enum.symm i).1 (enum.symm i).2).preimage_comp (coords (enum.symm i).1)

section Pullback

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)
  {JΓ : Language} [JΓ.Structure (Additive O.ValueGroupˣ)]
  (A : ∀ s, Set (CanonicalSort O s)) (S : RVValueSection O)
  (g : E → PositiveField K →* PositiveField K)
  (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

set_option linter.style.haveILetI false in
/-- The partition selected in the value language gives the positive
case of Lemma 2.29 when the value interpretation pulls its definitions
back to RV over the fixed base. -/
theorem FixedBaseAffinePartition.definable_pullback {m n : ℕ}
    (U : Set (I → Additive O.ValueGroupˣ)) :
    letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
    ∀ (W : Submodule E (Additive O.ValueGroupˣ))
      (Q : FixedBaseAffinePartition (J := JΓ) W U m n)
      (tag : Fin Q.count ↪ RV0 O), (∀ j, tag j ∈ A .rv) →
      (∀ γ ∈ W, S.representative γ.toMul ∈ A .rv) →
      (∀ D : Set (I → Additive O.ValueGroupˣ), (W : Set (Additive O.ValueGroupˣ)).Definable JΓ D →
        SortedDefinableOver (canonicalStructure (L := L) O hO P) A
          {x : ∀ s, RVVariables I s → CanonicalSort O s | x .rv ∈ positiveValuePullback O D}) →
      RVDefinablyEquivalent (canonicalStructure (L := L) O hO P) A
        (positiveValuePullback O U)
        (taggedRVUnion (fun j => affineRVTarget O (n := n) (positiveValuePullback O (Q.domain j))) tag) := by
  letI := unsignedValueModule O g P hP hzero hone hadd hmul hunit
  intro W Q tag htag hsection hpullback
  exact definable_affine_partition_pullback O hP hzero hone hadd hmul hunit hO A S
    Q.coordinates Q.domain Q.coefficients Q.translation
    (fun j i => hsection (Q.translation j i) (Q.translation_mem j i)) U tag htag
    Q.cover Q.disjoint (fun j => hpullback _ (Q.pieceDefinable j))

end Pullback

end GeneralizedEuler.Section2
