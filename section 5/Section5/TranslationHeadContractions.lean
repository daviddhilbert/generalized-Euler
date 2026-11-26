module

public import Section5.HeadContractionFromCenters

/-! A definable translation by a function of the retained field
coordinates is a head preparation on a family whose fibers are full
translated leading-term fibers. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K)

namespace UnaryPreparation

@[expose] def translated (c : K) : UnaryPreparation O (PreparationLabels O (RV0 O) 0) where
  label x := ULift.up (rv O (x-c))
  offset _ := c
  lead t := t.down
  leading _ := rfl
  constant_label h := congrArg ULift.up h

end UnaryPreparation

variable [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
  {E : Type*} [L.Structure (Residue O)] (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem translated_head_mapGraph_definable
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (c : (Fin n → K) → K)
    (defC : DefinableRelation 𝓜 S.carrier (fun (a : fieldAssignment n Z) (b : fieldAssignment 1 Z) =>
      c (a .vf) = b .vf 0)) :
    SortedDefinableOver 𝓜 S.carrier {a : SortedAssignment Z (HistoryGraphVariables n 0) |
      (UnaryPreparation.translated O (c (a .vf ∘ Sum.inr))).map (a .vf (.inl 0)) =
        (a .vf (.inl 1),decodeHistory O 0 (a .rv))} := by
  let U := HistoryGraphVariables n 0
  let V := MixedVariables 1 Empty
  let W := SumVariables U V
  let take : (s : TCsort) → SumVariables (MixedVariables n Empty) V s → W s
    | .vf => Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
    | .rv => Sum.elim Empty.elim Empty.elim
  let source : SortedTerm L E (WithBase S.carrier W) .vf := .var (.inr (.inl (.inl 0)))
  let target : SortedTerm L E (WithBase S.carrier W) .vf := .var (.inr (.inl (.inl 1)))
  let center : SortedTerm L E (WithBase S.carrier W) .vf := .var (.inr (.inr 0))
  have difference := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .vf (.inl (.inl 1)) (subVF F source center)
  have lead := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inl ()) (rvOfVF target)
  unfold DefinableRelation at defC
  convert definable_project_mixed ((defC.pullback_relabel take).inter (difference.inter lead)) using 1
  ext a
  have sub (u : SortedAssignment Z V) : (subVF F source center).realize 𝓜 (fun s => Sum.elim Subtype.val
      (appendAssignments a u s)) = a .vf (.inl 0) - u .vf 0 := by
    rw [eval_subVF O hO power F minusOne hm hF]
    rfl
  have leading (u : SortedAssignment Z V) : (rvOfVF target).realize 𝓜 (fun s => Sum.elim Subtype.val
      (appendAssignments a u s)) = rv O (a .vf (.inl 1)) := eval_rvOfVF O hO power _ _
  change (_ = _) ↔ ∃ u : SortedAssignment Z V, c (a .vf ∘ Sum.inr) = u .vf 0 ∧
    a .vf (.inl 1) = (subVF F source center).realize 𝓜 (fun s => Sum.elim Subtype.val (appendAssignments a u s)) ∧
    a .rv () = (rvOfVF target).realize 𝓜 (fun s => Sum.elim Subtype.val (appendAssignments a u s))
  simp only [sub,leading]
  change (((a .vf (.inl 0))-c (a .vf ∘ Sum.inr)),ULift.up (rv O (a .vf (.inl 0)-c (a .vf ∘ Sum.inr)))) =
      (a .vf (.inl 1),ULift.up (a .rv ())) ↔
    ∃ u : SortedAssignment Z V, c (a .vf ∘ Sum.inr) = u .vf 0 ∧
      a .vf (.inl 1) = a .vf (.inl 0)-u .vf 0 ∧ a .rv () = rv O (a .vf (.inl 1))
  constructor
  · intro eq
    obtain ⟨a₁,a₂⟩ := Prod.mk.inj eq
    refine ⟨fieldTupleAssignment (fun _ => c (a .vf ∘ Sum.inr)),rfl,a₁.symm,?_⟩
    exact (congrArg ULift.down a₂).symm.trans (congrArg (rv O) a₁)
  · rintro ⟨u,hc,hx,hv⟩
    apply Prod.ext
    · rw [hc,hx]
    · rw [hc,← hx,hv]

@[expose] def HeadContractionData.ofTranslation
    (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S (n+1) k)
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (c : (Fin n → K) → K)
    (defC : DefinableRelation 𝓜 S.carrier (fun (a : fieldAssignment n Z) (b : fieldAssignment 1 Z) =>
      c (a .vf) = b .vf 0))
    (stable : ∀ b x y (t : A.tags → RV0 O), rv O (x-c b) = rv O (y-c b) →
      ((x,b,t) ∈ A.verticalCarrier ↔ (y,b,t) ∈ A.verticalCarrier)) : HeadContractionData A where
  length := 0
  preparation b := UnaryPreparation.translated O (c b)
  mapGraph := translated_head_mapGraph_definable O hO power S F minusOne hm hF c defC
  historyGraph := vertical_history_graph_definable O hO power S (ℓ := 0) (I := A.tags)
    (fun b => UnaryPreparation.translated O (c b)) (translated_head_mapGraph_definable O hO power S F minusOne hm hF c defC)
  constant b x y t h := stable b x y t (congrArg ULift.down h)
  finiteOffsets b := by
    apply (Set.finite_singleton (c b)).subset
    rintro _ ⟨u,rfl⟩
    exact Set.mem_singleton _
  finalLead _ _ := rfl

end GeneralizedEuler.Section5
