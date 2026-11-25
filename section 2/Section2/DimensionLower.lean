module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Section2.DefinableCharts

/-! The lower bound on the VF arity of a definable injection. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

private theorem rank_le_arity_of_subset_closure {A : Type*} (B : Matroid A)
    {n k : ℕ} (x : Fin n → A) (y : Fin k → A)
    (h : Set.range x ⊆ B.closure (Set.range y)) : (B.eRk (Set.range x)).toNat ≤ k := by
  have hrk := (B.eRk_mono h).trans_eq (B.eRk_closure_eq (Set.range y))
  have hcard : (Set.range y).encard ≤ (k : ℕ∞) := by
    rw [← Set.image_univ]
    exact (Set.encard_image_le y Set.univ).trans_eq (by simp)
  have hle := (hrk.trans (B.eRk_le_encard _)).trans hcard
  simpa using ENat.toNat_le_toNat hle (by simp)

universe u v w z

/-- The lower bound in Lemma 2.26. The relative matroid is the exchange
pregeometry of VF over the field base. The rank comparison is the cited
weakly o-minimal dimension theorem. The closure hypothesis records the
forward use of the no-new-VF-points lemma from §3. -/
theorem vfDimension_le_arity_of_definable_embedding
    {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z} [TopologicalSpace (X .vf)]
    (M : SortedStructure L E X) (A : ∀ s, Set (X s)) {R S : Type} {n k : ℕ}
    (D : Set (∀ s, MixedVariables n R s → X s)) (hD : D.Nonempty)
    (f : D ↪ (∀ s, MixedVariables k S s → X s))
    (hf : SortedDefinableOver M A {a : ∀ s, (MixedVariables n R s ⊕ MixedVariables k S s) → X s |
      ∃ x : D, x.val = (fun s => a s ∘ Sum.inl) ∧ f x = (fun s => a s ∘ Sum.inr)})
    (B : Matroid (X .vf))
    (hrank : ∀ (y : R → X .rv), (sortedFiber (mixedTuple '' D) y).Nonempty →
      ∃ x ∈ sortedFiber (mixedTuple '' D) y, (B.eRk (Set.range x)).toNat =
        projectionDimension (sortedFiber (mixedTuple '' D) y))
    (hclosure : ∀ (p : ∀ s, MixedVariables n R s → X s) (q : ∀ s, MixedVariables k S s → X s),
      SortedDefinableOver M (fun s => A s ∪ Set.range (q s)) {p} →
      Set.range (p .vf) ⊆ B.closure (Set.range (q .vf))) :
    vfDimension (mixedTuple '' D) ≤ k := by
  obtain ⟨y, hne, hdim⟩ := exists_nonempty_fiber_projectionDimension_eq_vfDimension (hD.image mixedTuple)
  obtain ⟨x, hx, hxrank⟩ := hrank y hne
  change (x, y) ∈ mixedTuple '' D at hx
  obtain ⟨a, ha, hax⟩ := hx
  let b : D := ⟨a, ha⟩
  have hc := hclosure a (f b) (SortedDefinableOver.singleton_of_embedding_graph f hf b)
  have hk := rank_le_arity_of_subset_closure B (a .vf) (f b .vf) hc
  have hfield : a .vf = x := congrArg Prod.fst hax
  rwa [hfield, hxrank, hdim] at hk

end GeneralizedEuler.Section2
