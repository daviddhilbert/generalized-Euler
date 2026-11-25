module

public import Section3.FiberPartitions

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2 FirstOrder FirstOrder.Language
universe u
variable {L : Language.{u,u}} {E : Type u} {X V : TCsort → Type u}

/-- Two embeddings of a model into a common extension that agree on RV
and the base and identify these two tuples give equal leading terms.
One can take an embedding and its composite with the immediate
automorphism of 3.15 in a sufficiently saturated extension. -/
theorem same_branch_of_immediate_embeddings {Y : TCsort → Type u} {n : ℕ}
    {M : SortedStructure L E X} {N : SortedStructure L E Y} (v : ∀ s, V s → X s)
    (f g : SortedEmbedding M N) (rv : ∀ z, f.toEmbedding .rv z = g.toEmbedding .rv z)
    (base : ∀ s j, f.toEmbedding s (v s j) = g.toEmbedding s (v s j))
    (a b : Fin n → X .vf) (move : ∀ j, f.toEmbedding .vf (a j) = g.toEmbedding .vf (b j))
    (t : SortedTerm L E (AddSortedBlock V .vf n) .vf) : branchAt M v t a = branchAt M v t b := by
  apply (f.toEmbedding .rv).injective
  rw [rv (branchAt M v t b)]
  simp only [branchAt,SortedEmbedding.map_rv,SortedEmbedding.realize_term]
  congr 2
  funext s j
  rw [SortedEmbedding.mapAssignment_apply,SortedEmbedding.mapAssignment_apply]
  rcases j with j | ⟨j,⟨h⟩⟩
  · exact base s j
  · subst s; exact move j

/-- Lemma 3.26, assembled from the cut-disc point theorem over field
closure (3.19–3.21), immediate movement on polydiscs in one type (3.15),
and the closure dimension theorem for definable RV sets (2.27). The
comparison embeddings can take their values in a larger model. -/
theorem rv_boundary_dimension_lt (T : SortedTheory L E) (M : SortedStructure L E X)
    (v : ∀ s, V s → X s) (hne : ∀ s, Nonempty (X s)) (hT : ∀ φ ∈ T, φ.realize M)
    [Zero (X .rv)] [TopologicalSpace (X .rv)] [LinearOrder (X .rv)] [DenselyOrdered (X .rv)]
    [NoMinOrder (X .rv)] [NoMaxOrder (X .rv)] [OrderTopology (X .rv)]
    (zero : ∀ {W : TCsort → Type u} (p : ∀ s, W s → X s), rvZeroTerm.realize M p = 0)
    (point : ∀ {W : TCsort → Type u} (φ : SortedFormula L E (AddSortedVar W .vf)) (label : W .rv)
      (P : T.PointedModel W), P.realizes (cutFiberFormula φ label) →
      letI := valuedStructureOfSorted P.model ∅
      ∃ z ∈ Substructure.closure (convexLanguage L) (range (P.point .vf)), P.model.rvMap z = P.point .rv label)
    (immediate : ∀ n (P : T.PointedModel (FiberTestVars V n)),
      (∀ j, P.point .rv (fiberInput j) ≠ rvZeroTerm.realize P.model P.point) →
      (∀ χ : SortedFormula L E (AddSortedBlock V .vf n), ∀ a b : Fin n → P.carrier .vf,
        P.model.rvMap ∘ a = P.point .rv ∘ fiberInput → P.model.rvMap ∘ b = P.point .rv ∘ fiberInput →
        (χ.realize P.model (appendSortedBlock (baseOf P.point) a) ↔
          χ.realize P.model (appendSortedBlock (baseOf P.point) b))) →
      ∀ a b : Fin n → P.carrier .vf, P.model.rvMap ∘ a = P.point .rv ∘ fiberInput →
        P.model.rvMap ∘ b = P.point .rv ∘ fiberInput →
        ∃ (Y : TCsort → Type u) (N : SortedStructure L E Y) (f g : SortedEmbedding P.model N),
          (∀ z, f.toEmbedding .rv z = g.toEmbedding .rv z) ∧
          (∀ s j, f.toEmbedding s (baseOf P.point s j) = g.toEmbedding s (baseOf P.point s j)) ∧
          ∀ j, f.toEmbedding .vf (a j) = g.toEmbedding .vf (b j))
    (tame : ∀ d (B : Set (Fin d → X .rv)), BlockDefinable M v .rv B → interior B = ∅ → IsNowhereDense B)
    {d : ℕ} (A : Set (Fin d → X .vf)) (hA : BlockDefinable M v .vf A) :
    projectionDimensionWithBot (rvBoundary (fun a => M.rvMap ∘ a) A) < (d : WithBot ℕ) := by
  apply (definable_rv_boundary_dimension M v (fun _ _ => zero _) _ _ tame A hA).2
  · exact fun _ A h i => coordinate_branches_of_cut_points T M v hne hT point A h i
  · intro n t
    apply finite_term_fiber_partition T M v hne hT (fun _ => zero _) t univ
    intro P nz same a b ha hb
    obtain ⟨Y,N,f,g,rv,base,move⟩ := immediate n P nz (fun χ => same χ (mem_univ _)) a b ha hb
    exact same_branch_of_immediate_embeddings _ f g rv base a b move t

end GeneralizedEuler.Section3
