module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The affine trivialization from reviewed Lemma 2.29. The positive RV
group is written additively in this file. -/

public section

namespace GeneralizedEuler.Section2

open scoped BigOperators

variable {E G V : Type*} [Field E] [AddCommGroup G] [Module E G]
  [AddCommGroup V] [Module E V] {m n : ℕ}

/-- Apply a matrix over the exponent field and add a translation. -/
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

end GeneralizedEuler.Section2
