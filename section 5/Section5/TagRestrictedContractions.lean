module

public import Section5.HeadContractionIteration
public import Section4.Objects

/-! A contraction keeps every old RV tag. Restricting to a condition
on these tags therefore commutes with every step of a run. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ}

namespace RetainedFieldFamily

@[expose] def restrictTags (A : RetainedFieldFamily M S n k)
    (D : Set (A.tags → RV0 O)) (defD : isRVSet M S D) : RetainedFieldFamily M S n k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := {p ∈ A.carrier | p.2 ∈ D}
  definable :=
    let take : ∀ s, RVVariables A.tags s → MixedVariables n A.tags s
      | .vf => PEmpty.elim
      | .rv => id
    A.definable.inter (defD.pullback_relabel take)
  finiteFibers b v := (A.finiteFibers b v).subset (fun _ h => ⟨h.1.1,h.2⟩)

end RetainedFieldFamily

namespace HeadContractionData

variable {A : RetainedFieldFamily M S (n+1) k} (H : HeadContractionData A)
  (D : Set (A.tags → RV0 O)) (defD : isRVSet M S D)

@[expose] def restrictTags : HeadContractionData (A.restrictTags D defD) where
  length := H.length
  preparation := H.preparation
  mapGraph := H.mapGraph
  historyGraph := H.historyGraph
  constant b x y t e := and_congr_left' (H.constant b x y t e)
  finiteOffsets := H.finiteOffsets
  finalLead := H.finalLead

theorem restrictTags_target :
    (H.restrictTags D defD).target =
      H.target.restrictTags {q | q ∘ Sum.inr ∈ D} (isRVSet_precomp Sum.inr defD) := by
  have carrier : (H.restrictTags D defD).target.carrier =
      (H.target.restrictTags {q | q ∘ Sum.inr ∈ D} (isRVSet_precomp Sum.inr defD)).carrier := by
    ext x
    change (∃ a, ((a,x.1,x.2 ∘ Sum.inr) ∈ A.verticalCarrier ∧ x.2 ∘ Sum.inr ∈ D) ∧
      (H.preparation x.1).label a = decodeHistory O H.length (x.2 ∘ Sum.inl)) ↔
      ((∃ a, (a,x.1,x.2 ∘ Sum.inr) ∈ A.verticalCarrier ∧
      (H.preparation x.1).label a = decodeHistory O H.length (x.2 ∘ Sum.inl)) ∧ x.2 ∘ Sum.inr ∈ D)
    exact ⟨fun ⟨a,⟨ha,h⟩,eq⟩ => ⟨⟨a,ha,eq⟩,h⟩,fun ⟨⟨a,ha,eq⟩,h⟩ => ⟨a,⟨ha,h⟩,eq⟩⟩
  unfold HeadContractionData.target RetainedFieldFamily.restrictTags at carrier ⊢
  congr

end HeadContractionData

namespace HeadContractionRun

theorem restrictRuns_with_source {A : RetainedFieldFamily M S n k} {l : ℕ} {B : RetainedFieldFamily M S 0 l}
    (run : HeadContractionRun A B) :
    ∃ old : A.tags → B.tags,
    (∀ t : B.tags → RV0 O, (Fin.elim0,t) ∈ B.carrier → ∃ b, (b,t ∘ old) ∈ A.carrier) ∧
    ∀ (D : Set (A.tags → RV0 O)) (defD : isRVSet M S D),
      HeadContractionRun (A.restrictTags D defD)
        (B.restrictTags {t | t ∘ old ∈ D} (isRVSet_precomp old defD)) := by
  induction run with
  | done A =>
    refine ⟨id,fun t ht => ⟨Fin.elim0,ht⟩,?_⟩
    intro D defD
    exact .done _
  | next H tail ih =>
    obtain ⟨old,source,all⟩ := ih
    refine ⟨old ∘ Sum.inr,?_,?_⟩
    · intro t ht
      obtain ⟨b,hb⟩ := source t ht
      obtain ⟨x,hx,_⟩ := hb
      exact ⟨Fin.cons x b,hx⟩
    · intro D defD
      refine .next (H.restrictTags D defD) ?_
      rw [H.restrictTags_target]
      exact all _ _

theorem restrictRuns {A : RetainedFieldFamily M S n k} {l : ℕ} {B : RetainedFieldFamily M S 0 l}
    (run : HeadContractionRun A B) :
    ∃ old : A.tags → B.tags, ∀ (D : Set (A.tags → RV0 O)) (defD : isRVSet M S D),
      HeadContractionRun (A.restrictTags D defD)
        (B.restrictTags {t | t ∘ old ∈ D} (isRVSet_precomp old defD)) := by
  obtain ⟨old,_,runs⟩ := run.restrictRuns_with_source
  exact ⟨old,runs⟩

end HeadContractionRun

end GeneralizedEuler.Section5
