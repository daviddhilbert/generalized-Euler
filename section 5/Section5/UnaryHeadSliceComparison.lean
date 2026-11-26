module

public import Section5.UnaryHeadPullbacks
public import Section5.PreparedUnaryKernel

/-! Two unary contractions of the same retained family have common
blowups on each fixed old RV slice, by the fixed-base unary kernel. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Q" => RVVariables (Fin k)

variable {A B : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 1 k}
  (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B)

namespace HeadContractionData

@[expose] def unarySliceEquiv (v : Fin k → RV0 O) :
    {a : SortedAssignment Z (MixedVariables 1 H.target.tags) | mixedTuple a ∈ H.liftedSlice v} ≃ H.unarySlice v where
  toFun a := ⟨unaryPair O a.val,(H.unarySlice_iff_liftedSlice v a.val).2 a.property⟩
  invFun p := ⟨(fun s => match s with | .vf => fun _ => p.val.1 | .rv => p.val.2),by
    apply (H.unarySlice_iff_liftedSlice v _).1
    exact p.property⟩
  left_inv a := by
    apply Subtype.ext
    funext s i
    cases s
    · exact congrArg (a.val .vf) (Subsingleton.elim 0 i)
    · rfl
  right_inv _ := rfl

theorem unarySlices_definably_equivalent (p : SortedAssignment Z Q)
    (lifted : MixedDefinablyEquivalent 𝓜 ((𝓜).termGenerated (namedTuple S p))
      {a : SortedAssignment Z (MixedVariables 1 H.target.tags) | mixedTuple a ∈ H.liftedSlice (p .rv)}
      {b : SortedAssignment Z (MixedVariables 1 J.target.tags) | mixedTuple b ∈ J.liftedSlice (p .rv)}) :
    let T := (𝓜).termGenerated (namedTuple S p)
    ∃ e : H.unarySlice (p .rv) ≃ J.unarySlice (p .rv), UnaryMixedGraphDefinable O hO power T e := by
  intro T
  obtain ⟨f,df⟩ := lifted
  let a := H.unarySliceEquiv O hO power S (p .rv)
  let b := J.unarySliceEquiv O hO power S (p .rv)
  let e := a.symm.trans (f.trans b)
  refine ⟨e,df.congr ?_⟩
  intro u v
  constructor
  · rintro ⟨hu,eq⟩
    refine ⟨(H.unarySlice_iff_liftedSlice (p .rv) u).2 hu,?_⟩
    change (b (f (a.symm (a ⟨u,hu⟩)))).val = unaryPair O v
    rw [a.symm_apply_apply]
    exact congrArg (unaryPair O) eq
  · rintro ⟨hu,eq⟩
    let x : {u : SortedAssignment Z (MixedVariables 1 H.target.tags) | mixedTuple u ∈ H.liftedSlice (p .rv)} :=
      ⟨u,(H.unarySlice_iff_liftedSlice (p .rv) u).1 hu⟩
    refine ⟨x.property,?_⟩
    change (b (f (a.symm (a x)))).val = unaryPair O v at eq
    rw [a.symm_apply_apply] at eq
    funext s i
    cases s
    · change Fin 1 at i
      rw [Subsingleton.elim i (0 : Fin 1)]
      exact congrArg Prod.fst eq
    · exact congrFun (congrArg Prod.snd eq) i

end HeadContractionData

theorem unary_head_slice_classes_common_blowup (p : SortedAssignment Z Q)
    {m n : ℕ} (idx : Fin m ≃ Fin 1 ⊕ H.target.tags) (idy : Fin n ≃ Fin 1 ⊕ J.target.tags)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (neg : rv O (-1) ∈ S.carrier .rv)
    (sat : let T := (𝓜).termGenerated (namedTuple S p)
      ∀ I : Type, Finite I → RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables T.carrier I)
        (CenterTestAssignments T.carrier I))
    (immediate : let T := (𝓜).termGenerated (namedTuple S p)
      ∀ x y : K, (∀ c : T.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
        ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
          (∀ c ∈ T.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t)
    (charts : let T := (𝓜).termGenerated (namedTuple S p)
      ∀ f : H.unarySlice (p .rv) ≃ J.unarySlice (p .rv), UnaryMixedGraphDefinable O hO power T f →
        ∃ (I : Type) (_ : Finite I), Nonempty (UnaryChartPartition O hO power T f I))
    (lifted : MixedDefinablyEquivalent 𝓜 ((𝓜).termGenerated (namedTuple S p))
      {a : SortedAssignment Z (MixedVariables 1 H.target.tags) | mixedTuple a ∈ H.liftedSlice (p .rv)}
      {b : SortedAssignment Z (MixedVariables 1 J.target.tags) | mixedTuple b ∈ J.liftedSlice (p .rv)}) :
    let T := (𝓜).termGenerated (namedTuple S p)
    let nT : rv O (-1) ∈ T.carrier .rv :=
      ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
    letI := H.target.finiteTags
    letI := J.target.finiteTags
    CommonBlowup (ElementaryClassStep O hO power T nT)
      (unaryLabelClass O hO power T (H.unarySlice (p .rv)) idx (H.unarySlice_definable p)
        (H.unarySlice_pullback (p .rv)) (H.unarySlice_finite (p .rv)))
      (unaryLabelClass O hO power T (J.unarySlice (p .rv)) idy (J.unarySlice_definable p)
        (J.unarySlice_pullback (p .rv)) (J.unarySlice_finite (p .rv))) := by
  intro T nT
  obtain ⟨f,df⟩ := H.unarySlices_definably_equivalent O hO power S J p lifted
  obtain ⟨I,finite,⟨chart⟩⟩ := charts f df
  let := finite
  let := H.target.finiteTags
  let := J.target.finiteTags
  exact unary_common_blowup_of_chart_partition O hO power T F minusOne hm hF sat immediate he small nT
    f chart idx idy (H.unarySlice_definable p) (J.unarySlice_definable p) df
    (H.unarySlice_pullback (p .rv)) (J.unarySlice_pullback (p .rv)) (H.unarySlice_finite (p .rv)) (J.unarySlice_finite (p .rv))

end GeneralizedEuler.Section5
