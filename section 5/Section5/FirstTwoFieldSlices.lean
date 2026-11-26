module

public import Section5.TailFieldSlices

/-! Fix every field coordinate except the first pair. Restricting
the first head contraction to this slice commutes with fixing the
same tuple in its target. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ}

local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables n Empty

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily M S (n+2) k)

@[expose] def firstTwoCarrier (p : SortedAssignment Z P) : Set (PreparationPoint O (Fin 2) A.tags) :=
  {x | let b : Fin (n+2) → K := Fin.cons (x.1 0) (Fin.cons (x.1 1) (p .vf))
       (b,x.2) ∈ A.carrier}

@[expose] def firstTwoSlice (p : SortedAssignment Z P) :
    RetainedFieldFamily M (M.termGenerated (namedTuple S p)) 2 k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := A.firstTwoCarrier p
  definable := by
    let U := MixedVariables 2 A.tags
    let W := SumVariables P U
    let take : (s : TCsort) → MixedVariables (n+2) A.tags s → W s
      | .vf => Fin.cases (.inr 0) (Fin.cases (.inr 1) Sum.inl)
      | .rv => Sum.inr
    let raw := A.definable.pullback_relabel take
    convert definable_scheme_at_fiber p _ raw using 1
    ext a
    have eq : (fun i => appendAssignments p a .vf (take .vf i)) =
        Fin.cons (a .vf 0) (Fin.cons (a .vf 1) (p .vf)) := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases rfl (fun r => rfl) j
    change ((Fin.cons (a .vf 0) (Fin.cons (a .vf 1) (p .vf))),a .rv) ∈ A.carrier ↔
      ((fun i => appendAssignments p a .vf (take .vf i)),a .rv) ∈ A.carrier
    rw [eq]
  finiteFibers b v := by
    change {q : A.tags → RV0 O | (Fin.cons (b 0) (Fin.cons (b 1) (p .vf)),q) ∈ A.carrier ∧ q ∘ A.select = v}.Finite
    exact A.finiteFibers (Fin.cons (b 0) (Fin.cons (b 1) (p .vf))) v

end RetainedFieldFamily

namespace HeadContractionData

variable {A : RetainedFieldFamily M S (n+2) k} (H : HeadContractionData (n := n+1) A)

theorem mapGraph_at_two_slice (p : SortedAssignment Z P) :
    SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier
      {a : SortedAssignment Z (HistoryGraphVariables 1 H.length) |
        (H.preparation (Fin.cons (a .vf (.inr 0)) (p .vf))).map (a .vf (.inl 0)) =
          (a .vf (.inl 1),decodeHistory O H.length (a .rv))} := by
  let U := HistoryGraphVariables 1 H.length
  let W := SumVariables P U
  let take : (s : TCsort) → HistoryGraphVariables (n+1) H.length s → W s
    | .vf => Sum.elim (Sum.inr ∘ Sum.inl) (Fin.cases (.inr (.inr 0)) Sum.inl)
    | .rv => Sum.inr
  convert definable_scheme_at_fiber p _ (H.mapGraph.pullback_relabel take) using 1
  ext a
  let b : Fin (n+1) → K := fun i => appendAssignments p a .vf (take .vf (.inr i))
  have eq : b = Fin.cons (a .vf (.inr 0)) (p .vf) := by
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  change (H.preparation (Fin.cons (a .vf (.inr 0)) (p .vf))).map (a .vf (.inl 0)) = _ ↔
    (H.preparation b).map (a .vf (.inl 0)) = _
  rw [eq]
  rfl

theorem historyGraph_at_two_slice (p : SortedAssignment Z P) :
    DefinableRelation M (M.termGenerated (namedTuple S p)).carrier
      (fun (a : SortedAssignment Z (VerticalVariables 1 (A.firstTwoSlice p).tags))
        (u : SortedAssignment Z (RVVariables (HistoryIndex H.length))) =>
        (H.preparation (Fin.cons (a .vf (.inr 0)) (p .vf))).label (a .vf (.inl ())) = decodeHistory O H.length (u .rv)) := by
  let U := VerticalVariables 1 (A.firstTwoSlice p).tags
  let V := RVVariables (HistoryIndex H.length)
  let W := SumVariables P (SumVariables U V)
  let take : (s : TCsort) → SumVariables (VerticalVariables (n+1) A.tags) V s → W s
    | .vf => Sum.elim (Sum.elim (Sum.inr ∘ Sum.inl ∘ Sum.inl) (Fin.cases (.inr (.inl (.inr 0))) Sum.inl)) (Sum.inr ∘ Sum.inr)
    | .rv => Sum.inr
  have defH := H.historyGraph
  unfold DefinableRelation at defH ⊢
  convert definable_scheme_at_fiber p _ (defH.pullback_relabel take) using 1
  ext a
  let b : Fin (n+1) → K := fun i => appendAssignments p a .vf (take .vf (.inl (.inr i)))
  have eq : b = Fin.cons (a .vf (.inl (.inr 0))) (p .vf) := by
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  change (H.preparation (Fin.cons (a .vf (.inl (.inr 0))) (p .vf))).label (a .vf (.inl (.inl ()))) = _ ↔
    (H.preparation b).label (a .vf (.inl (.inl ()))) = _
  rw [eq]
  rfl

@[expose] def atFirstTwoSlice (p : SortedAssignment Z P) : HeadContractionData (n := 1) (A.firstTwoSlice p) where
  length := H.length
  preparation b := H.preparation (Fin.cons (b 0) (p .vf))
  mapGraph := H.mapGraph_at_two_slice p
  historyGraph := H.historyGraph_at_two_slice p
  constant b x y t h := H.constant (Fin.cons (b 0) (p .vf)) x y t h
  finiteOffsets b := H.finiteOffsets (Fin.cons (b 0) (p .vf))
  finalLead b := H.finalLead (Fin.cons (b 0) (p .vf))

theorem atFirstTwoSlice_target (p : SortedAssignment Z P) :
    (H.atFirstTwoSlice p).target = H.target.fieldTailSlice p := by
  rfl

end HeadContractionData

end GeneralizedEuler.Section5
