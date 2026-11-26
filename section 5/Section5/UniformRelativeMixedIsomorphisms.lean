module

public import Section5.RelativeMixedIsoSchemes
public import Section5.UniformFiberBijections

/-! Compactness chooses a finite definable partition on which the
named mixed graph matrices are valid. Each glued entry is definable
over the original base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}
  {I J : Type} [Finite I] [Finite J]
  (A : I → RelativeMixedCarrier M S P) (B : J → RelativeMixedCarrier M S P)

theorem uniform_relative_mixed_iso_scheme
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (D : Set (SortedAssignment X P)) (d : SortedDefinableOver M S.carrier D)
    (fiberIso : ∀ p ∈ D, (RelativeMixedCarrier.fibers A p).Iso (RelativeMixedCarrier.fibers B p)) :
    ∃ W : RelativeMixedIsoScheme A B, ∀ p ∈ D, W.valid p := by
  let good (W : RelativeMixedIsoScheme A B) : Set (SortedAssignment X P) := {p | W.valid p}
  obtain ⟨F,parts,defParts,sub,disj,cover⟩ := finite_definable_partition_of_cover sat D d good
    (fun W => W.valid_definable) (fun p hp => RelativeMixedIsoScheme.exists_of_fiber_iso p (fiberIso p hp))
  let T := {w // w ∈ F}
  let glue {U : TCsort → Type} (r : ∀ s, P s → U s) (sets : T → Set (SortedAssignment X U)) :=
    ⋃ t, sets t ∩ {x | (fun s => x s ∘ r s) ∈ parts t}
  have dg {U : TCsort → Type} (r : ∀ s, P s → U s) (sets : T → Set (SortedAssignment X U))
      (defSets : ∀ t, SortedDefinableOver M S.carrier (sets t)) :
      SortedDefinableOver M S.carrier (glue r sets) :=
    SortedDefinableOver.iUnion (fun t => (defSets t).inter ((defParts t).pullback_relabel r))
  let W : RelativeMixedIsoScheme A B :=
    { source i j := glue (fun _ => Sum.inl) (fun t => t.val.source i j)
      target j i := glue (fun _ => Sum.inl) (fun t => t.val.target j i)
      graph i j := glue (fun _ => Sum.inl ∘ Sum.inl) (fun t => t.val.graph i j)
      sourceDefinable i j := dg _ _ (fun t => t.val.sourceDefinable i j)
      targetDefinable j i := dg _ _ (fun t => t.val.targetDefinable j i)
      graphDefinable i j := dg _ _ (fun t => t.val.graphDefinable i j) }
  refine ⟨W,?_⟩
  intro p hp
  obtain ⟨t,ht⟩ := Set.mem_iUnion.1 (cover.symm ▸ hp)
  have hglue {U : TCsort → Type} (r : ∀ s, P s → U s) (sets : T → Set (SortedAssignment X U))
      (x : SortedAssignment X U) (base : (fun s => x s ∘ r s) = p) :
      x ∈ glue r sets ↔ x ∈ sets t := by
    constructor
    · intro h
      obtain ⟨z,hs,hz⟩ := Set.mem_iUnion.1 h
      have eq : z = t := by
        by_contra ne
        exact Set.disjoint_left.1 (disj ne) (base ▸ hz) ht
      rwa [eq] at hs
    · intro h
      have hp' : (fun s => x s ∘ r s) ∈ parts t := base.symm ▸ ht
      exact Set.mem_iUnion.2 ⟨t,h,hp'⟩
  have left (i : I) (j : J) (u : SortedAssignment X (A i).vars) :
      appendAssignments p u ∈ W.source i j ↔ appendAssignments p u ∈ t.val.source i j :=
    hglue (fun _ => Sum.inl) _ (appendAssignments p u) rfl
  have right (j : J) (i : I) (v : SortedAssignment X (B j).vars) :
      appendAssignments p v ∈ W.target j i ↔ appendAssignments p v ∈ t.val.target j i :=
    hglue (fun _ => Sum.inl) _ (appendAssignments p v) rfl
  have g (i : I) (j : J) (u : SortedAssignment X (A i).vars) (v : SortedAssignment X (B j).vars) :
      appendAssignments (appendAssignments p u) v ∈ W.graph i j ↔
      appendAssignments (appendAssignments p u) v ∈ t.val.graph i j :=
    hglue (fun _ => Sum.inl ∘ Sum.inl) _ (appendAssignments (appendAssignments p u) v) rfl
  have ok : t.val.valid p := sub t ht
  refine ⟨fun i => ?_,fun j => ?_,fun i j => ?_⟩
  · simpa only [FiberPartitionScheme,left] using ok.1 i
  · simpa only [FiberPartitionScheme,right] using ok.2.1 j
  · simpa only [FiberBijectionScheme,left,right,g] using ok.2.2 i j

end GeneralizedEuler.Section5
