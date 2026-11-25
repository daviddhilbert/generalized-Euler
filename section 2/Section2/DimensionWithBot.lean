module

public import Section2.Dimension
public import Mathlib.Order.WithBot

public section

namespace GeneralizedEuler.Section2

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- The dimension of an empty set is minus infinity. On nonempty sets
the natural number supplied by the projection or VF arity calculation
is the dimension. -/
noncomputable def dimensionWithBot {α : Type*} (D : Set α) (arity : ℕ) : WithBot ℕ := by
  classical
  exact if D.Nonempty then (arity : WithBot ℕ) else ⊥

@[simp] theorem dimensionWithBot_empty {α : Type*} (arity : ℕ) :
    dimensionWithBot (∅ : Set α) arity = ⊥ := by simp [dimensionWithBot]

theorem dimensionWithBot_of_nonempty {α : Type*} {D : Set α} (hD : D.Nonempty) (arity : ℕ) :
    dimensionWithBot D arity = (arity : WithBot ℕ) := by simp [dimensionWithBot,hD]

@[simp] theorem dimensionWithBot_eq_bot_iff {α : Type*} {D : Set α} {k : ℕ} :
    dimensionWithBot D k = ⊥ ↔ D = ∅ := by
  rcases D.eq_empty_or_nonempty with rfl | h
  · simp
  · simp [dimensionWithBot_of_nonempty h,h.ne_empty]

noncomputable abbrev projectionDimensionWithBot (D : Set (Fin n → X)) : WithBot ℕ :=
  dimensionWithBot D (projectionDimension D)

noncomputable abbrev vfDimensionWithBot {Y : Type*} (D : Set ((Fin n → X) × Y)) : WithBot ℕ :=
  dimensionWithBot D (vfDimension D)

/-- The projection formula in 2.25, including the empty set. -/
theorem projectionDimensionWithBot_eq_coe_iff {D : Set (Fin n → X)} {k : ℕ} :
    projectionDimensionWithBot D = (k : WithBot ℕ) ↔
      HasInteriorProjection (k := k) D ∧ projectionDimension D ≤ k := by
  rcases D.eq_empty_or_nonempty with rfl | hD
  · simp [projectionDimensionWithBot,HasInteriorProjection]
  · rw [projectionDimensionWithBot, dimensionWithBot_of_nonempty hD, WithBot.coe_inj]
    constructor
    · rintro rfl
      exact ⟨hasInteriorProjection_projectionDimension hD,le_rfl⟩
    · rintro ⟨h,h'⟩
      exact h'.antisymm (le_projectionDimension h)

/-- For every finite dimension, an RV fiber attaining it exists. -/
theorem vfDimensionWithBot_attained {Y : Type*} {D : Set ((Fin n → X) × Y)} {k : ℕ}
    (h : vfDimensionWithBot D = (k : WithBot ℕ)) :
    ∃ y, projectionDimensionWithBot (sortedFiber D y) = (k : WithBot ℕ) := by
  rcases D.eq_empty_or_nonempty with rfl | hD
  · simp [vfDimensionWithBot] at h
  rw [vfDimensionWithBot,dimensionWithBot_of_nonempty hD,WithBot.coe_inj] at h
  obtain ⟨y,hy,he⟩ := exists_nonempty_fiber_projectionDimension_eq_vfDimension hD
  exact ⟨y,(dimensionWithBot_of_nonempty hy _).trans (congrArg _ (he.trans h))⟩

end GeneralizedEuler.Section2
