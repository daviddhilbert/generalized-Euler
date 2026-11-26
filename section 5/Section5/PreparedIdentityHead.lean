module

public import Section5.PreparedHeadFamilies
public import Section5.IdentityOnHead

/-! After preparation an identity head removes the normalized field
coordinate. Its additional RV coordinate duplicates the recorded
leading term of the preparation. -/

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

variable {A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S (n+1) k}
    (H : HeadContractionData A)
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (zero : S.carrier .vf) (hz : zero.val = 0)

@[expose] def preparedIdentity : HeadContractionData H.preparedFamily :=
  .identityOnHead O hO power S H.preparedFamily F minusOne hm hF zero hz H.prepared_head_stable

local notation "J" => preparedIdentity O hO power S H F minusOne hm hF zero hz

theorem preparedIdentity_target_mem (p : Fin n → K) (t : (J).target.tags → RV0 O) :
    (p,t) ∈ (J).target.carrier ↔
    (p,t ∘ Sum.inr) ∈ H.target.carrier ∧ t (.inl ()) = t (.inr (.inl (lastIndex H.length))) := by
  change (∃ x, ((p,t ∘ Sum.inr) ∈ H.target.carrier ∧ rv O x = t (.inr (.inl (lastIndex H.length)))) ∧
    ULift.up (rv O (x-zero.val)) = ULift.up (t (.inl ()))) ↔ _
  simp only [hz,sub_zero,ULift.up.injEq]
  constructor
  · rintro ⟨x,⟨h,e⟩,f⟩
    exact ⟨h,f.symm.trans e⟩
  · rintro ⟨h,e⟩
    obtain ⟨x,hx⟩ := rv_surjective O (t (.inl ()))
    exact ⟨x,⟨h,hx.trans e⟩,hx⟩

end HeadContractionData

end GeneralizedEuler.Section5
