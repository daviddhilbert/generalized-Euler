module

public import Section5.PreparedFieldRowEndpoints

/-! The classes of the descended field rows sum to the two groups
of actual terminal supports, with the new leading term omitted
precisely on its zero stratum. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language RelativeObjectFamily

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k a h : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 1 k)
  (idx : Fin a ≃ A.tags) (cs : List (S.carrier .vf)) (e : Fin h ≃ HistoryIndex cs.length)

local notation "T" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs

theorem prepared_ordered_field_rows_gluedClass
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    (contains : ∀ p u, appendAssignments p u ∈ A.fieldFiberTags idx → p ∈ D)
    (same : ∀ x y (t : A.tags → RV0 O), (T).label x = (T).label y →
      (((fun _ => x),t) ∈ A.carrier ↔ ((fun _ => y),t) ∈ A.carrier))
    (zero : S.carrier .rv) (hz : zero.val = 0)
    (new : Bool) (bounds : Finset (Fin k) → ℕ)
    (I : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h new.toNat)
    (index : I.labels = {q ∈ preparedHistoryLabels O hO power S cs e D |
      q (e.symm (lastIndex cs.length)) ≠ 0 ↔ new = true}) :
    let H := HeadContractionData.ofUnaryCenters O hO power S A cs minusOne hm F hF same
    let defH := preparedHistoryRelation_definable O hO power S cs e F minusOne hm hF defD
    let W := fun i => (A.orderedFieldFiberRows idx zero bounds i).descend defH
    ∀ (v : ∀ q ∈ I.labels, Valid W zero (rvTupleAssignment q)),
      gluedClass zero hz I W v =
        ∑ s : Finset (Fin k), objectClass 𝓜 S (H.target.terminalGradedPiece (preparedHeadTagOrder O hO power S A idx cs e)
          (extendTerminalSupport s new) zero hz) := by
  intro H defH W v
  let f (s : Finset (Fin k)) := objectClass 𝓜 S (H.target.terminalGradedPiece
    (preparedHeadTagOrder O hO power S A idx cs e) (extendTerminalSupport s new) zero hz)
  let order := RetainedFieldFamily.fieldFiberSupportIndex (k := k)
  calc
    gluedClass zero hz I W v = ∑ i, f (order i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact prepared_field_row_gluedClass O hO power S A idx cs e minusOne hm F hF D defD contains same
        zero hz (order i) new (bounds (order i)) I index (fun q hq => v q hq i)
    _ = _ := Fintype.sum_equiv order _ _ (fun _ => rfl)

end GeneralizedEuler.Section5
