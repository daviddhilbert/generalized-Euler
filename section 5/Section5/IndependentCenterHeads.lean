module

public import Section5.HeadContractionFromCenters

/-! A unary preparation can be used in every complementary field
fiber when its labels already decide the relevant membership tests. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

variable (cs : List (S.carrier .vf))

local notation "T" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs

theorem independent_centers_mapGraph_definable
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    SortedDefinableOver 𝓜 S.carrier {a : SortedAssignment Z (HistoryGraphVariables n cs.length) |
      (T).map (a .vf (.inl 0)) = (a .vf (.inl 1),decodeHistory O cs.length (a .rv))} := by
  let ren : (s : TCsort) → MixedVariables 2 (HistoryIndex cs.length) s → HistoryGraphVariables n cs.length s
    | .vf => Sum.inl
    | .rv => id
  exact (preparationGraph_definable O hO power S F minusOne hm hF cs).pullback_relabel ren

@[expose] def HeadContractionData.ofIndependentCenters
    (A : RetainedFieldFamily 𝓜 S (n+1) k)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (same : ∀ b x y t, (T).label x = (T).label y →
      ((x,b,t) ∈ A.verticalCarrier ↔ (y,b,t) ∈ A.verticalCarrier)) : HeadContractionData A where
  length := cs.length
  preparation _ := T
  mapGraph := independent_centers_mapGraph_definable O hO power S cs minusOne hm F hF
  historyGraph := vertical_history_graph_definable O hO power S (fun _ => T)
    (independent_centers_mapGraph_definable O hO power S cs minusOne hm F hF)
  constant := same
  finiteOffsets _ := UnaryPreparation.finite_prepared_offsets Subtype.val cs
  finalLead _ := lead_decode_history O Subtype.val cs

end GeneralizedEuler.Section5
