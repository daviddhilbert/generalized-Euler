module

public import Section5.HeadContractionSlices

/-! Fix the remaining field tuple in a head contraction. The original
preparation is a unary head contraction over the generated base, and
its terminal tags are the corresponding fiber of the original target. -/

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

variable (A : RetainedFieldFamily M S (n+1) k)

@[expose] def fieldTailSliceCarrier (p : SortedAssignment Z P) : Set (PreparationPoint O (Fin 1) A.tags) :=
  {x | let fields : Fin (n+1) → K := Fin.cons (x.1 0) (p .vf)
       (fields,x.2) ∈ A.carrier}

@[expose] def fieldTailSlice (p : SortedAssignment Z P) :
    RetainedFieldFamily M (M.termGenerated (namedTuple S p)) 1 k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := A.fieldTailSliceCarrier p
  definable := by
    let U := MixedVariables 1 A.tags
    let W := SumVariables P U
    let take : (s : TCsort) → MixedVariables (n+1) A.tags s → W s
      | .vf => Fin.cases (.inr 0) (fun i => .inl i)
      | .rv => Sum.inr
    have all := A.definable.pullback_relabel take
    convert definable_scheme_at_fiber p _ all using 1
    ext a
    have eq : (fun i => appendAssignments p a .vf (take .vf i)) = Fin.cons (a .vf 0) (p .vf) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    change (Fin.cons (a .vf 0) (p .vf),a .rv) ∈ A.carrier ↔
      ((fun i => appendAssignments p a .vf (take .vf i)),a .rv) ∈ A.carrier
    rw [eq]
  finiteFibers b v := by
    change {q : A.tags → RV0 O | (Fin.cons (b 0) (p .vf),q) ∈ A.carrier ∧ q ∘ A.select = v}.Finite
    exact A.finiteFibers (Fin.cons (b 0) (p .vf)) v

end RetainedFieldFamily

namespace HeadContractionData

variable {A : RetainedFieldFamily M S (n+1) k} (H : HeadContractionData A)

theorem mapGraph_at_field_tail (p : SortedAssignment Z P) :
    SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier
      {a : SortedAssignment Z (HistoryGraphVariables 0 H.length) |
        (H.preparation (p .vf)).map (a .vf (.inl 0)) = (a .vf (.inl 1),decodeHistory O H.length (a .rv))} := by
  let U := HistoryGraphVariables 0 H.length
  let W := SumVariables P U
  let take : (s : TCsort) → HistoryGraphVariables n H.length s → W s
    | .vf => Sum.elim (Sum.inr ∘ Sum.inl) Sum.inl
    | .rv => Sum.inr
  exact definable_scheme_at_fiber p _ (H.mapGraph.pullback_relabel take)

theorem historyGraph_at_field_tail (p : SortedAssignment Z P) :
    DefinableRelation M (M.termGenerated (namedTuple S p)).carrier
      (fun (a : SortedAssignment Z (VerticalVariables 0 (A.fieldTailSlice p).tags))
        (u : SortedAssignment Z (RVVariables (HistoryIndex H.length))) =>
        (H.preparation (p .vf)).label (a .vf (.inl ())) = decodeHistory O H.length (u .rv)) := by
  let U := VerticalVariables 0 A.tags
  let V := RVVariables (HistoryIndex H.length)
  let W := SumVariables P (SumVariables U V)
  let take : (s : TCsort) → SumVariables (VerticalVariables n A.tags) V s → W s
    | .vf => Sum.elim (Sum.elim (Sum.inr ∘ Sum.inl ∘ Sum.inl) Sum.inl) (Sum.inr ∘ Sum.inr)
    | .rv => Sum.inr
  unfold DefinableRelation
  exact definable_scheme_at_fiber p _ (H.historyGraph.pullback_relabel take)

@[expose] def atFieldTail (p : SortedAssignment Z P) : HeadContractionData (n := 0) (A.fieldTailSlice p) where
  length := H.length
  preparation := fun _ => H.preparation (p .vf)
  mapGraph := H.mapGraph_at_field_tail p
  historyGraph := H.historyGraph_at_field_tail p
  constant _ x y t h := H.constant (p .vf) x y t h
  finiteOffsets _ := H.finiteOffsets (p .vf)
  finalLead _ := H.finalLead (p .vf)

theorem atFieldTail_target (p : SortedAssignment Z P) (u : HistoryIndex H.length ⊕ A.tags → RV0 O) :
    (Fin.elim0,u) ∈ (H.atFieldTail p).target.carrier ↔ (p .vf,u) ∈ H.target.carrier := by
  change (∃ x, (x,Fin.elim0,u ∘ Sum.inr) ∈ (A.fieldTailSlice p).verticalCarrier ∧
    (H.preparation (p .vf)).label x = decodeHistory O H.length (u ∘ Sum.inl)) ↔
    (∃ x, (x,p .vf,u ∘ Sum.inr) ∈ A.verticalCarrier ∧
      (H.preparation (p .vf)).label x = decodeHistory O H.length (u ∘ Sum.inl))
  rfl

end HeadContractionData

end GeneralizedEuler.Section5
