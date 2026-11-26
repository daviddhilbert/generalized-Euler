module

public import Section5.RecordedFieldLabels
public import Section5.VerticalPositioning
public import Section5.PreparedMapOperations

/-! Recording a head history before changing field coordinates gives
full translated leading-term fibers in the original coordinates. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}

namespace HeadContractionData

variable {A : RetainedFieldFamily M S (n+1) k} (H : HeadContractionData A)

local notation "Z" => CanonicalSort O

@[expose] def historyCode (a : SortedAssignment Z (MixedVariables (n+1) A.tags)) :
    HistoryIndex H.length → RV0 O :=
  encodeHistory O H.length ((H.preparation (a .vf ∘ Fin.succ)).label (a .vf 0))

theorem historyCode_graph :
    DefinableRelation M S.carrier
      (fun (a : SortedAssignment Z (MixedVariables (n+1) A.tags))
        (r : SortedAssignment Z (RVVariables (HistoryIndex H.length))) =>
        H.historyCode a = r .rv) := by
  let U := MixedVariables (n+1) A.tags
  let V := RVVariables (HistoryIndex H.length)
  let take : (s : TCsort) → SumVariables (VerticalVariables n A.tags) V s → SumVariables U V s
    | .vf => Sum.elim (Sum.inl ∘ Sum.elim (fun _ => 0) Fin.succ) Sum.inr
    | .rv => id
  have h := H.historyGraph
  unfold DefinableRelation at h ⊢
  convert h.pullback_relabel take using 1
  ext a
  change encodeHistory O H.length ((H.preparation (a .vf ∘ Sum.inl ∘ Fin.succ)).label (a .vf (.inl 0))) =
    a .rv ∘ Sum.inr ↔
    (H.preparation (a .vf ∘ Sum.inl ∘ Fin.succ)).label (a .vf (.inl 0)) =
      decodeHistory O H.length (a .rv ∘ Sum.inr)
  constructor
  · intro e
    rw [← e,decode_encode_history]
  · intro e
    rw [e,encode_decode_history]

@[expose] def recordedFamily : RetainedFieldFamily M S (n+1) k :=
  A.withRecordedLabels H.historyCode H.historyCode_graph

@[expose] def recordedCenter (b : Fin n → K) (q : HistoryIndex H.length ⊕ A.tags → RV0 O) : K :=
  (H.preparation b).offset (decodeHistory O H.length (q ∘ Sum.inl))

theorem recordedFamily_position (b : Fin n → K) (q : HistoryIndex H.length ⊕ A.tags → RV0 O) (x : K) :
    (x,b,q) ∈ H.recordedFamily.verticalCarrier ↔
      (b,q) ∈ H.target.carrier ∧ rv O (x - H.recordedCenter b q) = q (.inl (lastIndex H.length)) := by
  let T := H.preparation b
  let w := decodeHistory O H.length (q ∘ Sum.inl)
  let D : Set K := {x | (x,b,q ∘ Sum.inr) ∈ A.verticalCarrier}
  obtain ⟨a,ha⟩ := mixedTuple_surjective (O := O) (Fin.cons x b,q)
  have h := A.recordedCarrier_mem H.historyCode a
  have first : a .vf = Fin.cons x b := congrArg Prod.fst ha
  have second : a .rv = q := congrArg Prod.snd ha
  have pair : mixedTuple (A.recordedForget a) = (Fin.cons x b,q ∘ Sum.inr) :=
    Prod.ext first (congrArg (· ∘ Sum.inr) second)
  have hist : H.historyCode (A.recordedForget a) = encodeHistory O H.length (T.label x) := by
    change encodeHistory O H.length ((H.preparation (a .vf ∘ Fin.succ)).label (a .vf 0)) = _
    rw [first]
    rfl
  have lhs : (x,b,q) ∈ H.recordedFamily.verticalCarrier ↔ x ∈ D ∧ T.label x = w := by
    change (Fin.cons x b,q) ∈ A.recordedCarrier H.historyCode ↔ _
    rw [← ha,h,pair,hist,second]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro e
      change T.label x = decodeHistory O H.length (q ∘ Sum.inl)
      rw [← e,decode_encode_history]
    · intro e
      rw [e]
      exact encode_decode_history O H.length _
  have lead : T.lead w = q (.inl (lastIndex H.length)) := H.finalLead b (q ∘ Sum.inl)
  refine lhs.trans ?_
  have e := T.restricted_label_fiber O D (fun u v eq => H.constant b u v (q ∘ Sum.inr) eq) w x
  rw [lead] at e
  exact e

end HeadContractionData

end GeneralizedEuler.Section5
