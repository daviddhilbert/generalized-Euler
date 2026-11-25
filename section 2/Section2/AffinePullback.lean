module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Lattice.Disjoint

/-! The affine trivialization from reviewed Lemma 2.29. The positive RV
group is written additively in this file. -/

public section

namespace GeneralizedEuler.Section2

open scoped BigOperators

variable {E G V : Type*} [Field E] [AddCommGroup G] [Module E G]
  [AddCommGroup V] [Module E V] {m n : ℕ}

/-- Apply a matrix over the exponent field and add a translation. -/
@[expose]
def affineCoordinates {A : Type*} [AddCommGroup A] [Module E A]
    (M : Fin n → Fin m → E) (b : Fin n → A) (x : Fin m → A) (i : Fin n) : A :=
  b i + ∑ j, M i j • x j

theorem map_affineCoordinates (v : G →ₗ[E] V) (M : Fin n → Fin m → E)
    (u : Fin n → G) (x : Fin m → G) (i : Fin n) :
    v (affineCoordinates M u x i) = affineCoordinates M (v ∘ u) (v ∘ x) i := by
  simp only [affineCoordinates, map_add, map_sum, LinearMap.map_smul, Function.comp_apply]

/-- In the fixed-base version, intercepts chosen in the image of the base
subspace admit representatives in that same subspace. A zero translation
uses the zero representative, which is the multiplicative RV unit. -/
theorem exists_affineTranslation_in_base (v : G →ₗ[E] V) (W : Submodule E G)
    (δ : Fin n → V) (hδ : ∀ i, δ i ∈ W.map v) :
    ∃ u : Fin n → G, (∀ i, u i ∈ W) ∧ v ∘ u = δ ∧
      (∀ i, δ i = 0 → u i = 0) := by
  classical
  have lift : ∀ i, ∃ x ∈ W, v x = δ i ∧ (δ i = 0 → x = 0) := by
    intro i
    by_cases h : δ i = 0
    · exact ⟨0, W.zero_mem, (map_zero v).trans h.symm, fun _ => rfl⟩
    · obtain ⟨x, hx, hval⟩ := hδ i
      exact ⟨x, hx, hval, fun hzero => (h hzero).elim⟩
  choose u huW huv huz using lift
  exact ⟨u, huW, funext huv, huz⟩

/-- The pullback of the graph of one affine value-group piece. -/
abbrev affineGraphPullback (v : G →ₗ[E] V) (D : Set (Fin m → V))
    (M : Fin n → Fin m → E) (δ : Fin n → V) :=
  {p : (Fin m → G) × (Fin n → G) //
    v ∘ p.1 ∈ D ∧ ∀ i, v (p.2 i) = affineCoordinates M δ (v ∘ p.1) i}

/-- The pullback of a piece is the product of the projected pullback
with one copy of the residue kernel per omitted coordinate. Subtraction
in these coordinates is division by the manuscript's monomial lift. -/
def affineGraphPullbackEquiv (v : G →ₗ[E] V) (D : Set (Fin m → V))
    (M : Fin n → Fin m → E) (δ : Fin n → V) (u : Fin n → G) (hu : v ∘ u = δ) :
    affineGraphPullback v D M δ ≃ (Fin n → v.ker) × {x : Fin m → G // v ∘ x ∈ D} where
  toFun p := ⟨fun i => ⟨p.val.2 i - affineCoordinates M u p.val.1 i, by
      rw [LinearMap.mem_ker, map_sub, map_affineCoordinates, hu, p.property.2, sub_self]⟩,
    ⟨p.val.1, p.property.1⟩⟩
  invFun p := ⟨⟨p.2.val, fun i => (p.1 i : G) + affineCoordinates M u p.2.val i⟩,
    p.2.property, fun i => by
      rw [map_add, map_affineCoordinates, hu, LinearMap.mem_ker.mp (p.1 i).property, zero_add]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact sub_add_cancel _ _
  right_inv p := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact add_sub_cancel_right _ _
    · rfl

/-- An affine piece of the value set in the chosen coordinate order. -/
def affineValueGraph (D : Set (Fin m → V)) (M : Fin n → Fin m → E) (δ : Fin n → V) :
    Set ((Fin m → V) × (Fin n → V)) :=
  {p | p.1 ∈ D ∧ ∀ i, p.2 i = affineCoordinates M δ p.1 i}

def valueTupleMap (v : G →ₗ[E] V) (p : (Fin m → G) × (Fin n → G)) :
    (Fin m → V) × (Fin n → V) :=
  (v ∘ p.1, v ∘ p.2)

/-- The affine chart equivalences of Lemma 2.29 assemble along a
given disjoint partition of the value set. -/
noncomputable def affineGraphPartitionPullbackEquiv {l : ℕ}
    (v : G →ₗ[E] V) (U : Set ((Fin m → V) × (Fin n → V)))
    (D : Fin l → Set (Fin m → V)) (M : Fin l → Fin n → Fin m → E)
    (δ : Fin l → Fin n → V) (u : Fin l → Fin n → G) (hu : ∀ j, v ∘ u j = δ j)
    (hcover : U = ⋃ j, affineValueGraph (D j) (M j) (δ j))
    (hdisj : Pairwise (fun j k => Disjoint (affineValueGraph (D j) (M j) (δ j))
      (affineValueGraph (D k) (M k) (δ k)))) :
    (valueTupleMap v ⁻¹' U : Set _) ≃
      Σ j : Fin l, (Fin n → v.ker) × {x : Fin m → G // v ∘ x ∈ D j} := by
  let C (j : Fin l) := valueTupleMap v ⁻¹' affineValueGraph (D j) (M j) (δ j)
  have hpre : valueTupleMap v ⁻¹' U = ⋃ j, C j := by rw [hcover, Set.preimage_iUnion]
  have hd : Pairwise (fun j k => Disjoint (C j) (C k)) := by
    intro j k hjk
    exact Set.disjoint_left.mpr (fun _ h₁ h₂ => Set.disjoint_left.mp (hdisj hjk) h₁ h₂)
  exact (Set.equivOfEq hpre).trans
    ((Set.unionEqSigmaOfDisjoint hd).trans
      (Equiv.sigmaCongrRight fun j => affineGraphPullbackEquiv v (D j) (M j) (δ j) (u j) (hu j)))

/-- A base-valued affine partition can use all translation representatives
in the same base subspace. -/
theorem exists_base_affinePartition_lifts {l : ℕ} (v : G →ₗ[E] V) (W : Submodule E G)
    (δ : Fin l → Fin n → V) (hδ : ∀ j i, δ j i ∈ W.map v) :
    ∃ u : Fin l → Fin n → G, (∀ j i, u j i ∈ W) ∧ (∀ j, v ∘ u j = δ j) ∧
      ∀ j i, δ j i = 0 → u j i = 0 := by
  choose u hW hu hz using fun j => exists_affineTranslation_in_base v W (δ j) (hδ j)
  exact ⟨u, hW, hu, hz⟩

end GeneralizedEuler.Section2
