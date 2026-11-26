module

public import Section5.UnaryPreparation

/-! Gluing preparations on the suffix over a prepared first coordinate.
The available suffix labels and the RV graph tests must descend to the
retained labels of the first coordinate. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] {O : ValuationSubring K}
  {H X Y U : Type*} (P : UnaryPreparation O H)

@[expose] def gluedPreparation (T : K → X → Y) (a : K × X) : (K × H) × Y :=
  (P.map a.1, T a.1 a.2)

theorem gluedPreparation_injective (T : K → X → Y) (hT : ∀ x, Function.Injective (T x)) :
    Function.Injective (gluedPreparation P T) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ he
  have hf : P.map a = P.map b := congrArg Prod.fst he
  obtain rfl : a = b := P.map_injective hf
  have hxy : T a x = T a y := congrArg Prod.snd he
  exact Prod.ext rfl (hT a hxy)

/-- The glued image consists of full fibers in both blocks. The suffix
fiberwise input specifies which suffix labels exist over each prepared
first-coordinate label. -/
theorem gluedPreparation_image (T : K → X → Y) (q : Y → U)
    (A : Set (K × X)) (labels : H → Set U)
    (hT : ∀ a, T a '' {x | (a, x) ∈ A} = q ⁻¹' labels (P.label a)) :
    gluedPreparation P T '' A =
      {b | b.1 ∈ Set.range P.map ∧ q b.2 ∈ labels b.1.2} := by
  ext b
  rcases b with ⟨⟨a, t⟩, y⟩
  constructor
  · rintro ⟨⟨x, z⟩, hz, h⟩
    have hm : P.map x = (a, t) := congrArg Prod.fst h
    have hq : T x z = y := congrArg Prod.snd h
    refine ⟨⟨x, hm⟩, ?_⟩
    have ht : P.label x = t := congrArg Prod.snd hm
    have hy : y ∈ T x '' {z | (x, z) ∈ A} := ⟨z, hz, hq⟩
    rw [hT x, Set.mem_preimage, ht] at hy
    exact hy
  · rintro ⟨⟨x, hx⟩, hy⟩
    have ht : P.label x = t := congrArg Prod.snd hx
    have hmem : y ∈ T x '' {z | (x, z) ∈ A} := by
      rw [hT x, Set.mem_preimage, ht]
      exact hy
    obtain ⟨z, hz, h⟩ := hmem
    exact ⟨(x, z), hz, Prod.ext hx h⟩

/-- All the original output tests descend through the glued map once
both the suffix output and its dependence on the prefix are expressed
in the two prepared labels. -/
theorem gluedPreparation_contracts {W : Type*} (T : K → X → Y) (q : Y → U)
    (A : Set (K × X)) (f : K × X → W) (contract : H → U → W)
    (hf : ∀ a ∈ A, f a = contract (P.label a.1) (q (T a.1 a.2))) :
    ∀ a ∈ A, ∀ b ∈ A,
      ((gluedPreparation P T a).1.2, q (gluedPreparation P T a).2) =
        ((gluedPreparation P T b).1.2, q (gluedPreparation P T b).2) → f a = f b := by
  intro a ha b hb h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  rw [hf a ha, hf b hb]
  exact congrArg₂ contract h₁ h₂

end GeneralizedEuler.Section5
