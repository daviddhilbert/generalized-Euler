module

public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.ModelTheory.Definability

/-! Definability and power boundedness in §2.1. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w

abbrev PositiveField (K : Type w) [Zero K] [LT K] := {x : K // 0 < x}

variable {L : Language.{u, v}} {K : Type w} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [L.Structure K]

/-- The graph of a field map, with the domain made explicit for partial maps. -/
def fieldGraph (D : Set K) (f : K → K) : Set (K × K) :=
  {p | p.1 ∈ D ∧ p.2 = f p.1}

/-- The graph of a power function has domain the positive multiplicative group. -/
def powerGraph (g : PositiveField K →* PositiveField K) : Set (K × K) :=
  {p | ∃ h : 0 < p.1, p.2 = (g ⟨p.1, h⟩ : K)}

/-- Definition 2.2 over a prescribed set of parameters. Taking `A = Set.univ`
gives the convention of §2.1. -/
def IsPowerBoundedOver (L : Language.{u, v}) [L.Structure K] (A : Set K) : Prop :=
  ∀ f : K → K, A.Definable₂ L (fieldGraph Set.univ f) →
    ∃ g : PositiveField K →* PositiveField K,
      A.Definable₂ L (powerGraph g) ∧
      ∃ b : K, ∀ x : PositiveField K, b < (x : K) → |f x| ≤ (g x : K)

abbrev IsPowerBounded (L : Language.{u, v}) [L.Structure K] : Prop :=
  IsPowerBoundedOver L (Set.univ : Set K)

/-- A bound definable over fewer parameters can also be used over a larger base. -/
theorem powerBound_over_larger_base {A B : Set K} (hAB : A ⊆ B)
    {g : PositiveField K →* PositiveField K}
    (hg : A.Definable₂ L (powerGraph g)) : B.Definable₂ L (powerGraph g) :=
  Set.Definable.mono hg hAB

/-- A unary cell with endpoints in the ambient order, allowing unbounded intervals. -/
def IsUnaryCell (s : Set K) : Prop :=
  s = Set.univ ∨ (∃ a, s = {a}) ∨ (∃ a, s = Set.Iio a) ∨
    (∃ a, s = Set.Ioi a) ∨ (∃ a b, s = Set.Ioo a b)

/-- O-minimality with arbitrary parameters as in Convention 2.1. -/
def IsOMinimal (L : Language.{u, v}) [L.Structure K] : Prop :=
  ∀ s : Set K, (Set.univ : Set K).Definable₁ L s →
    ∃ cells : Finset (Set K), (∀ c ∈ cells, IsUnaryCell c) ∧ s = ⋃ c ∈ cells, c

/-- The power-boundedness condition on all ordered real closed models of `T`. -/
def IsPowerBoundedTheory (T : L.Theory) : Prop :=
  ∀ (M : Type w) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [IsRealClosed M]
    [L.Structure M] [M ⊨ T], IsPowerBounded (K := M) L

end GeneralizedEuler.Section2
