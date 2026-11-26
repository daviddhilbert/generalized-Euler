module

public import Section5.TranslationHeadContractions
public import Section5.NamedFieldFunctions
public import Section5.HeadContractionIteration

/-! An identity head on a pullback records the original leading term.
The property of being a pullback in the remaining field coordinates
survives the step. -/

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

namespace RetainedFieldFamily

@[expose] def IsFieldPullback
    (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S n k) : Prop :=
  ∀ (x y : Fin n → K) (t : A.tags → RV0 O),
    (rv O ∘ x) = (rv O ∘ y) → ((x,t) ∈ A.carrier ↔ (y,t) ∈ A.carrier)

end RetainedFieldFamily

namespace HeadContractionData

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S (n+1) k)
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (zero : S.carrier .vf) (hz : zero.val = 0)
    (pullback : A.IsFieldPullback O hO power S)

@[expose] def identityHead : HeadContractionData A :=
  .ofTranslation O hO power S A F minusOne hm hF (fun _ => zero.val) (named_field_value_graph zero) (by
    intro b x y t e
    apply pullback
    funext j
    refine Fin.cases ?_ (fun _ => rfl) j
    change rv O x = rv O y
    simpa only [hz,sub_zero] using e)

local notation "H" => identityHead O hO power S A F minusOne hm hF zero hz pullback

theorem identityHead_target_iff (b : Fin n → K) (t : (H).target.tags → RV0 O) :
    (b,t) ∈ (H).target.carrier ↔
      ∃ x, (Fin.cons x b,t ∘ Sum.inr) ∈ A.carrier ∧ rv O x = t (.inl ()) := by
  change (∃ x, (Fin.cons x b,t ∘ Sum.inr) ∈ A.carrier ∧
    ULift.up (rv O (x-zero.val)) = ULift.up (t (.inl ()))) ↔ _
  simp only [hz,sub_zero,ULift.up.injEq]

theorem identityHead_target_pullback :
    (H).target.IsFieldPullback O hO power S := by
  intro x y t e
  rw [identityHead_target_iff,identityHead_target_iff]
  apply exists_congr
  intro a
  refine and_congr_left' (pullback _ _ _ ?_)
  funext j
  exact Fin.cases rfl (fun i => congrFun e i) j

end HeadContractionData

end GeneralizedEuler.Section5
