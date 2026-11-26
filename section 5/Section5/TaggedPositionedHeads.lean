module

public import Section5.TaggedHeadTranslations
public import Section5.IdentityOnHead

/-! Translate a full positioned fiber using its original tags.
An identity head then records its paradigm and drops the translated
field coordinate. -/

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

namespace HeadContractionData

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S (n+1) k)
  (c : (Fin n → K) → (A.tags → RV0 O) → K)
  (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
  (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
  (defC : DefinableRelation (canonicalStructure (L := L) O hO power) S.carrier
    (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables n A.tags))
      (v : fieldAssignment 1 (CanonicalSort O)) => c (a .vf) (a .rv) = v .vf 0))
  (finite : ∀ b, (Set.range (c b)).Finite)
  (B : Set (PreparationPoint O (Fin n) A.tags)) (u : (A.tags → RV0 O) → RV0 O)
  (shape : ∀ x b t, (x,b,t) ∈ A.verticalCarrier ↔ (b,t) ∈ B ∧ rv O (x-c b t) = u t)

local notation "P" => A.taggedTranslatedHead O hO power S c F minusOne hm hF defC finite

include shape in
theorem taggedTranslatedHead_vertical_mem (x : K) (b : Fin n → K) (t : A.tags → RV0 O) :
    (x,b,t) ∈ (P).verticalCarrier ↔ (b,t) ∈ B ∧ rv O x = u t := by
  change (Fin.cons (x + c b t) b,t) ∈ A.carrier ↔ _
  have h := shape (x + c b t) b t
  rw [add_sub_cancel_right] at h
  exact h

variable (zero : S.carrier .vf) (hz : zero.val = 0)

@[expose] def taggedPositionHead : HeadContractionData (P) :=
  .identityOnHead O hO power S (P) F minusOne hm hF zero hz (by
    intro b x y t h
    have a := taggedTranslatedHead_vertical_mem O hO power S A c F minusOne hm hF defC finite B u shape x b t
    have z := taggedTranslatedHead_vertical_mem O hO power S A c F minusOne hm hF defC finite B u shape y b t
    exact a.trans ((and_congr_right fun _ => (congrArg (· = u t) h).to_iff).trans z.symm))

local notation "H" => taggedPositionHead O hO power S A c F minusOne hm hF defC finite B u shape zero hz

theorem taggedPositionHead_target_mem (b : Fin n → K) (t : Unit ⊕ A.tags → RV0 O) :
    (b,t) ∈ (H).target.carrier ↔ (b,t ∘ Sum.inr) ∈ B ∧ t (.inl ()) = u (t ∘ Sum.inr) := by
  refine (identityOnHead_target_mem O hO power S (P) F minusOne hm hF zero hz _ b t).trans ?_
  have each (x : K) :=
    taggedTranslatedHead_vertical_mem O hO power S A c F minusOne hm hF defC finite B u shape x b (t ∘ Sum.inr)
  constructor
  · rintro ⟨x,h,e⟩
    obtain ⟨hb,hu⟩ := (each x).1 h
    exact ⟨hb,e.symm.trans hu⟩
  · rintro ⟨hb,he⟩
    obtain ⟨x,hx⟩ := rv_surjective O (t (.inl ()))
    exact ⟨x,(each x).2 ⟨hb,hx.trans he⟩,hx⟩

end HeadContractionData

end GeneralizedEuler.Section5
