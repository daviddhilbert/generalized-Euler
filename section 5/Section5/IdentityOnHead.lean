module

public import Section5.TranslationHeadContractions
public import Section5.NamedFieldFunctions

/-! The coordinate being contracted may already be a pullback
even when the remaining field coordinates are arbitrary. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n k : ℕ}

namespace HeadContractionData

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S (n+1) k)
  (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
  (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
  (zero : S.carrier .vf) (hz : zero.val = 0)
  (same : ∀ b x y t, rv O x = rv O y → ((x,b,t) ∈ A.verticalCarrier ↔ (y,b,t) ∈ A.verticalCarrier))

@[expose] def identityOnHead : HeadContractionData A :=
  .ofTranslation O hO power S A F minusOne hm hF (fun _ => zero.val) (named_field_value_graph zero)
    (fun b x y t e => same b x y t (by simpa only [hz,sub_zero] using e))

local notation "H" => identityOnHead O hO power S A F minusOne hm hF zero hz same

theorem identityOnHead_target_mem (p : Fin n → K) (t : Unit ⊕ A.tags → RV0 O) :
    (p,t) ∈ (H).target.carrier ↔
      ∃ x, (x,p,t ∘ Sum.inr) ∈ A.verticalCarrier ∧ rv O x = t (.inl ()) := by
  change (∃ x, (x,p,t ∘ Sum.inr) ∈ A.verticalCarrier ∧
    ULift.up (rv O (x-zero.val)) = ULift.up (t (.inl ()))) ↔ _
  simp only [hz,sub_zero,ULift.up.injEq]

end HeadContractionData

end GeneralizedEuler.Section5
