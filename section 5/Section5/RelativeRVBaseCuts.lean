module

public import Section5.RelativeRVObjectSchemes
public import Section5.GradedLiftTotalBijections

/-! A relative object supported on a definable base part is
extended by empty fibers on the rest of the base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.RelativeRVObjectScheme

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}
  (W : RelativeRVObjectScheme M S P)
  (D : Set (SortedAssignment X P)) (d : SortedDefinableOver M S.carrier D)

@[expose] def restrictBase : RelativeRVObjectScheme M S P where
  data := ⟨W.data.degree,W.data.arity,onlyOver D W.data.tags,onlyOver_definable d W.data.definable⟩
  graph := {x ∈ W.graph | (fun s => x s ∘ Sum.inl ∘ Sum.inl) ∈ D}
  definable := W.definable.inter (d.pullback_relabel (fun _ => Sum.inl ∘ Sum.inl))
  bound := W.bound

theorem restrictBase_valid (zero : S.carrier .rv) (p : SortedAssignment X P)
    (hyp : p ∈ D → W.valid zero p) : (W.restrictBase D d).valid zero p := by
  by_cases h : p ∈ D
  · have H := hyp h
    unfold RelativeRVObjectScheme.valid at H ⊢
    have tag (u : SortedAssignment X W.data.Vars) :
        appendAssignments p u ∈ (W.restrictBase D d).data.tags ↔ appendAssignments p u ∈ W.data.tags :=
      onlyOver_fiber_iff h u
    have graph (u : SortedAssignment X W.data.Vars) (v : labelAssignment W.data.degree X) :
        appendAssignments (appendAssignments p u) v ∈ (W.restrictBase D d).graph ↔
        appendAssignments (appendAssignments p u) v ∈ W.graph :=
      ⟨And.left,fun hg => ⟨hg,h⟩⟩
    refine ⟨fun u => (tag u).trans ((H.1 u).trans (exists_congr (fun v => (graph u v).symm))),
      fun u v w hv hw => H.2.1 u v w ((graph u v).1 hv) ((graph u w).1 hw),
      fun u v hv => H.2.2.1 u v ((graph u v).1 hv),?_⟩
    exact fun v a ha => H.2.2.2 v a (fun i => (graph (a i) v).1 (ha i))
  · refine ⟨fun u => ?_,fun u v w hv _ => (h hv.2).elim,
      fun u v hv => (h hv.2).elim,fun v a ha => (h (ha 0).2).elim⟩
    constructor
    · intro hu
      exact (h hu.2).elim
    · rintro ⟨v,hv⟩
      exact (h hv.2).elim

theorem restrictBase_relativeLift :
    relativeRVLift (M := M) (W.restrictBase D d).graph =
      onlyOver D (relativeRVLift (M := M) W.graph) :=
  rfl

end GeneralizedEuler.Section5.RelativeRVObjectScheme
