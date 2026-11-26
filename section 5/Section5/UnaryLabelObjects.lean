module

public import Section5.UnaryFiniteFibers
public import Section5.DefinableUnaryGrading
public import Section4.ValueFactorMap

/-! The unary label space yields actual degree-zero and degree-one
RV objects by splitting the zero leading term from the active ones. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I : Type} {m : ℕ} (A : Set (K × (I → RV0 O))) (idx : Fin m ≃ Fin 1 ⊕ I)

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def reindexedUnaryLabels : Set (Fin m → RV0 O) :=
  {t | t ∘ idx.symm ∈ unaryLabelSet O A}

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem reindexedUnaryLabels_finite (full : IsUnaryPullback O A) (finite : UnaryFiniteFibers A)
    (lead : RV0 O) : {t ∈ reindexedUnaryLabels O A idx | t (idx.symm (.inl 0)) = lead}.Finite := by
  let g (r : I → RV0 O) : Fin m → RV0 O := Sum.elim (fun _ => lead) r ∘ idx
  apply ((unaryLeadFibers_finite O full finite lead).image g).subset
  rintro t ⟨ht,hl⟩
  obtain ⟨a,ha,he⟩ := ht
  have hrv : rv O (a .vf 0) = lead := (congrFun he (.inl 0)).trans hl
  refine ⟨a .rv,⟨a .vf 0,ha,hrv⟩,?_⟩
  funext j
  let i := idx j
  have eq : t (idx.symm i) = t j := congrArg t (idx.symm_apply_apply j)
  have lab : encodeUnaryLabel O (unaryPair O a) i = t (idx.symm i) := congrFun he i
  change Sum.elim (fun _ => lead) (a .rv) i = t j
  rw [← eq,← lab]
  cases i
  · exact hrv.symm
  · rfl

variable [Finite I]

theorem reindexedUnaryLabels_definable (defA : UnaryPullbackDefinable O hO power S A) :
    isRVSet 𝓜 S (reindexedUnaryLabels O A idx) :=
  isRVSet_precomp idx.symm (unaryLabelSet_definable O hO power S defA)

@[expose] def unaryLabelObjects (defA : UnaryPullbackDefinable O hO power S A)
    (full : IsUnaryPullback O A) (finite : UnaryFiniteFibers A) : RVObject 𝓜 S 0 × RVObject 𝓜 S 1 :=
  let D := reindexedUnaryLabels O A idx
  let i := idx.symm (.inl 0)
  let hd := reindexedUnaryLabels_definable O hO power S A idx defA
  let hf := reindexedUnaryLabels_finite O A idx full finite
  (unaryDegreeZero O hO power S D i hd hf,unaryDegreeOne O hO power S D i hd hf)

@[expose] def unaryLabelClass (defA : UnaryPullbackDefinable O hO power S A)
    (full : IsUnaryPullback O A) (finite : UnaryFiniteFibers A) : RVSemiring 𝓜 S :=
  let U := unaryLabelObjects O hO power S A idx defA full finite
  objectClass 𝓜 S ⟨0,U.1⟩ + objectClass 𝓜 S ⟨1,U.2⟩

end GeneralizedEuler.Section5
