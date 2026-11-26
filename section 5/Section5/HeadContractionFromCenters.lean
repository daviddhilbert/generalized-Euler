module

public import Section5.HeadContractionFamilies

/-! A common list of unary preparation centers can be used as a head
contraction whenever membership is constant on its full histories. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 1 k)
  (cs : List (S.carrier .vf))

local notation "T" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs

theorem unary_centers_mapGraph_definable
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    SortedDefinableOver 𝓜 S.carrier {a : SortedAssignment Z (HistoryGraphVariables 0 cs.length) |
      (T).map (a .vf (.inl 0)) = (a .vf (.inl 1),decodeHistory O cs.length (a .rv))} := by
  let take : (s : TCsort) → MixedVariables 2 (HistoryIndex cs.length) s → HistoryGraphVariables 0 cs.length s
    | .vf => Sum.inl
    | .rv => id
  exact (preparationGraph_definable O hO power S F minusOne hm hF cs).pullback_relabel take

@[expose] def HeadContractionData.ofUnaryCenters
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (same : ∀ x y (t : A.tags → RV0 O), (T).label x = (T).label y →
      (((fun _ => x),t) ∈ A.carrier ↔ ((fun _ => y),t) ∈ A.carrier)) : HeadContractionData (n := 0) A where
  length := cs.length
  preparation _ := T
  mapGraph := unary_centers_mapGraph_definable O hO power S cs minusOne hm F hF
  historyGraph := vertical_history_graph_definable O hO power S (fun _ => T)
    (unary_centers_mapGraph_definable O hO power S cs minusOne hm F hF)
  constant b x y t h := by
    have const (a : K) : Fin.cons a b = fun _ => a := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      rfl
    change (Fin.cons x b,t) ∈ A.carrier ↔ (Fin.cons y b,t) ∈ A.carrier
    rw [const x,const y]
    exact same x y t h
  finiteOffsets _ := UnaryPreparation.finite_prepared_offsets Subtype.val cs
  finalLead _ := lead_decode_history O Subtype.val cs

end GeneralizedEuler.Section5
