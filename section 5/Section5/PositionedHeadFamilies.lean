module

public import Section5.RecordedHeadHistories
public import Section5.DefinableLiftLabels

/-! The coordinates of the original leading-term polydisc and the
positioning history can both be recorded over the fixed base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

section LeadingTerms

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {n k : ℕ}
  (A : RetainedFieldFamily M S n k)

local notation "Z" => CanonicalSort O

theorem RetainedFieldFamily.fieldLeadsGraph :
    DefinableRelation M S.carrier (fun
      (a : SortedAssignment Z (MixedVariables n A.tags)) (r : SortedAssignment Z (RVVariables (Fin n))) =>
      M.rvMap ∘ a .vf = r .rv) := by
  let W := SumVariables (MixedVariables n A.tags) (RVVariables (Fin n))
  let take : (s : TCsort) → SumVariables (MixedVariables n Empty) (RVVariables (Fin n)) s → W s
    | .vf => Sum.elim Sum.inl Sum.inr
    | .rv => Sum.elim Empty.elim Sum.inr
  have g := fieldLead_definable (M := M) (S := S) (n := n)
  unfold DefinableRelation at g ⊢
  convert g.pullback_relabel take using 1
  ext a
  change M.rvMap ∘ a .vf ∘ Sum.inl = a .rv ∘ Sum.inr ↔
    fieldLead M (fun s => (a s ∘ take s) ∘ Sum.inl) = (fun s => (a s ∘ take s) ∘ Sum.inr)
  constructor
  · intro eq
    funext s i
    cases s
    · exact i.elim
    · exact congrFun eq i
  · intro eq
    exact congrFun eq .rv

@[expose] def RetainedFieldFamily.withFieldLeads : RetainedFieldFamily M S n k :=
  A.withRecordedLabels (fun a => M.rvMap ∘ a .vf) A.fieldLeadsGraph

theorem RetainedFieldFamily.withFieldLeads_has_leading_terms
    (a : SortedAssignment Z (MixedVariables n A.withFieldLeads.tags))
    (ha : mixedTuple a ∈ A.withFieldLeads.carrier) (i : Fin n) :
    M.rvMap (a .vf i) = a .rv (.inl i) :=
  congrFun ((A.recordedCarrier_mem (fun a => M.rvMap ∘ a .vf) a).1 ha).2 i

end LeadingTerms

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n k : ℕ} {A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S (n+1) k}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem HeadContractionData.recordedCenter_graph (H : HeadContractionData A)
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment Z (MixedVariables n (HistoryIndex H.length ⊕ A.tags)))
        (r : fieldAssignment 1 Z) =>
        (a .vf,a .rv) ∈ H.target.carrier ∧ H.recordedCenter (a .vf) (a .rv) = r .vf 0) := by
  let U := MixedVariables n (A.tags ⊕ HistoryIndex H.length)
  let U' := MixedVariables n (HistoryIndex H.length ⊕ A.tags)
  let V := MixedVariables 1 Empty
  let take : (s : TCsort) → SumVariables U V s → SumVariables U' V s
    | .vf => id
    | .rv => Sum.map Sum.swap id
  have h := verticalPositioningGraph_definable O hO power S F minusOne hm hF H.preparation
    A.verticalCarrier A.verticalCarrier_definable H.mapGraph
  unfold DefinableRelation at h ⊢
  convert h.pullback_relabel take using 1
  ext a
  let p : Fin n → K := a .vf ∘ Sum.inl
  let t : HistoryIndex H.length ⊕ A.tags → RV0 O := a .rv ∘ Sum.inl
  let q := decodeHistory O H.length (t ∘ Sum.inl)
  simp only [Set.mem_ofPred_eq,verticalPositioningGraph]
  let p' := (a .vf ∘ take .vf) ∘ Sum.inl
  let t' := ((a .rv ∘ take .rv) ∘ Sum.inl) ∘ Sum.inl
  let q' := decodeHistory O H.length (((a .rv ∘ take .rv) ∘ Sum.inl) ∘ Sum.inr)
  have hp : p' = p := rfl
  have ht : t' = t ∘ Sum.inr := funext (fun _ => rfl)
  have hq : q' = q := congrArg (decodeHistory O H.length) (funext (fun _ => rfl))
  change ((∃ x, (x,p,t ∘ Sum.inr) ∈ A.verticalCarrier ∧ (H.preparation p).label x = q) ∧
      (H.preparation p).offset q = a .vf (.inr 0)) ↔
    ((∃ x, (x,p',t') ∈ A.verticalCarrier ∧ (H.preparation p').label x = q') ∧
      (H.preparation p').offset q' = a .vf (.inr 0))
  rw [hp,ht,hq]

end GeneralizedEuler.Section5
