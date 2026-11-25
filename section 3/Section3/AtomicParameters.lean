module

public import Section3.Atomicity

public section

namespace GeneralizedEuler.Section3

open Set

variable {X V C I : Type*} {D : Set (Set X)} {A : Set X}

/-- Lemma 3.12. A code consists of a scheme index and its chosen tuple.
Canonical choice on the nonempty image supplies a base-definable code fiber.
The same code then works at every point of the atom. -/
theorem atomic_after_naming_value (ha : AtomicOver D A) (v : V)
    (named : Set (Set X)) (hA : A ∈ named)
    (encode : ∀ B ∈ named, ∃ (c : X → C) (decode : C → V → Prop),
      (∀ x ∈ A, x ∈ B ↔ decode (c x) v) ∧
      ∃ w ∈ c '' A, c ⁻¹' {w} ∈ D) : AtomicOver named A := by
  refine ⟨hA, ha.2.nonempty, ?_⟩
  intro B hB x hx y hy
  obtain ⟨c, decode, he, w, hw, hf⟩ := encode B hB
  have h := ha.2.constant_code c hw hf
  exact (he x hx).trans (by rw [h x hx, ← h y hy]; exact (he y hy).symm)

/-- Lemma 3.18. Values use the additive order here. Each formula has
separate eventual truth values on the two sides of zero. Atomicity after
naming its bound transfers both tests, then saturation bounds all formulas. -/
theorem atomic_for_small_field_parameter {K Γ : Type*} [Zero K] [LinearOrder K] [Preorder Γ]
    (val : K → Γ) (test : I → X → K → Prop) (A : Set X) (hne : A.Nonempty)
    (germ : ∀ i x, x ∈ A → ∃ b : Γ, ∃ pos neg : Prop, ∀ e, b < val e → e ≠ 0 →
      (test i x e ↔ if 0 < e then pos else neg))
    (transfer : ∀ i b (pos neg : Prop),
      let B := {x | ∀ e, b < val e → e ≠ 0 → (test i x e ↔ if 0 < e then pos else neg)}
      ∀ x ∈ A, ∀ y ∈ A, x ∈ B ↔ y ∈ B)
    (bound : ∀ b : I → Γ, ∃ β, ∀ i, b i ≤ β)
    (named : K → Set (Set X)) (hdef : ∀ e, A ∈ named e)
    (hform : ∀ e B, B ∈ named e → ∃ i, ∀ x ∈ A, x ∈ B ↔ test i x e) :
    ∃ β, ∀ e, β < val e → e ≠ 0 → AtomicOver (named e) A := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  choose b pos neg hg using fun i => germ i x₀ hx₀
  obtain ⟨β, hβ⟩ := bound b
  refine ⟨β, fun e he he₀ => ⟨hdef e, ⟨x₀, hx₀⟩, ?_⟩⟩
  intro B hB x hx y hy
  obtain ⟨i, hi⟩ := hform e B hB
  have atPoint (z : X) (hz : z ∈ A) :
      test i z e ↔ if 0 < e then pos i else neg i :=
    ((transfer i (b i) (pos i) (neg i) x₀ hx₀ z hz).mp (hg i)) e ((hβ i).trans_lt he) he₀
  exact (hi x hx).trans ((atPoint x hx).trans ((atPoint y hy).symm.trans (hi y hy).symm))

end GeneralizedEuler.Section3
