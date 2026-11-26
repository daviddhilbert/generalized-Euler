module

public import Section2.SortedDefinability
public import Section5.FiniteCenters

/-! Compactness for the disagreement formula in Lemma 5.4. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

variable {L : Language} {E : Type*} {X : TCsort → Type*}
  (M : SortedStructure L E X) (V : TCsort → Type*) (W : Set (∀ s, V s → X s))

/-- The instance of saturation for a finite tuple of variables over a fixed
assignment of the named parameters. `W` specifies those assignments. -/
def RealizesFinitelySatisfiableTypes : Prop :=
  ∀ Δ : Set (SortedFormula L E V),
    (∀ U : Finset (SortedFormula L E V), (U : Set _) ⊆ Δ →
      ∃ x ∈ W, ∀ φ ∈ U, φ.realize M x) →
    ∃ x ∈ W, ∀ φ ∈ Δ, φ.realize M x

/-- If the whole type rules out disagreement, then finitely many of its
tests already do so. The finite tests belong to the original index set. -/
theorem finite_tests {I : Type*} (sat : RealizesFinitelySatisfiableTypes M V W)
    (different : SortedFormula L E V) (test : I → SortedFormula L E V)
    (hall : ∀ x ∈ W, (∀ i, (test i).realize M x) → ¬ different.realize M x) :
    ∃ C : Finset I, ∀ x ∈ W, (∀ i ∈ C, (test i).realize M x) → ¬ different.realize M x := by
  classical
  by_contra! h
  let Δ := insert different (Set.range test)
  have hf (U : Finset (SortedFormula L E V)) (hU : (U : Set _) ⊆ Δ) :
      ∃ x ∈ W, ∀ φ ∈ U, φ.realize M x := by
    let U' := U.filter (· ≠ different)
    have hU' : (U' : Set _) ⊆ test '' Set.univ := by
      intro φ hφ
      rw [Set.image_univ]
      obtain ⟨hφU, hne⟩ := Finset.mem_filter.mp hφ
      exact (hU hφU).resolve_left hne
    obtain ⟨C, _, hC⟩ := Finset.subset_set_image_iff.mp hU'
    obtain ⟨x, hx, hc, hd⟩ := h C
    refine ⟨x, hx, fun φ hφ => ?_⟩
    by_cases he : φ = different
    · exact he.symm ▸ hd
    · have hmem : φ ∈ C.image test := hC ▸ Finset.mem_filter.mpr ⟨hφ, he⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
      exact hc i hi
  obtain ⟨x, hx, hΔ⟩ := sat Δ hf
  exact hall x hx (fun i => hΔ _ (Or.inr (Set.mem_range_self i))) (hΔ _ (Or.inl rfl))

end GeneralizedEuler.Section5
