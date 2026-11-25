module

public import Section2.LeadingTermOrder
public import Mathlib.ModelTheory.Definability

/-! Weak o-minimality passes to the RV sort through the monotone quotient,
as in Remark 2.27. -/

public section

namespace GeneralizedEuler.Section2

variable {X Y : Type*} [LinearOrder X] [LinearOrder Y]

/-- A unary set is a finite union of convex subsets of its order. -/
def FiniteConvexUnion (D : Set X) : Prop :=
  ∃ (n : ℕ) (C : Fin n → Set X), (∀ i, Set.OrdConnected (C i)) ∧ D = ⋃ i, C i

theorem convex_image_of_monotone_surjective {f : X → Y}
    (hf : Monotone f) (hs : Function.Surjective f) {C : Set X} (hC : Set.OrdConnected C) :
    Set.OrdConnected (f '' C) := by
  refine ⟨?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ t ⟨hxt, hty⟩
  rcases hxt.eq_or_lt with rfl | hxt
  · exact ⟨x, hx, rfl⟩
  rcases hty.eq_or_lt with rfl | hty
  · exact ⟨y, hy, rfl⟩
  obtain ⟨z, rfl⟩ := hs t
  have hxz : x ≤ z := (hf.reflect_lt hxt).le
  have hzy : z ≤ y := (hf.reflect_lt hty).le
  exact ⟨z, hC.out hx hy ⟨hxz, hzy⟩, rfl⟩

/-- The unary weak o-minimality implication needed for an ordered quotient. -/
theorem finiteConvexUnion_of_preimage {f : X → Y} (hf : Monotone f)
    (hs : Function.Surjective f) {D : Set Y} (hD : FiniteConvexUnion (f ⁻¹' D)) :
    FiniteConvexUnion D := by
  obtain ⟨n, C, hC, h⟩ := hD
  refine ⟨n, fun i => f '' C i, fun i => convex_image_of_monotone_surjective hf hs (hC i), ?_⟩
  rw [← Set.image_iUnion, ← h, Set.image_preimage_eq _ hs]

set_option linter.style.haveILetI false in
/-- Boundedness by finitely many convex sets in VF gives the same property
for its RV image once the pullback is known to be VF-definable. -/
theorem rv_finiteConvexUnion_of_preimage {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O)
    (D : Set (RV0 O)) (hD : FiniteConvexUnion (rv O ⁻¹' D)) :
    letI := rvLinearOrder O hO
    FiniteConvexUnion D := by
  letI := rvLinearOrder O hO
  exact finiteConvexUnion_of_preimage
    (fun _ _ h => (rv_le_rv_iff O hO).mpr (Or.inl h)) (rv_surjective O) hD

end GeneralizedEuler.Section2
