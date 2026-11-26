module

public import Section5.PreparedFieldFamilyEndpoints
public import Section5.PreparedFieldRowConstancy
public import Section5.GluedPreparedBlowupPaths
public import Section5.UnaryLifting

/-! The unary fieldwise comparison uses one preparation of the named
witness paths. The glued endpoints are the actual contractions of the
two retained families under this common preparation. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language
  RelativeObjectFamily RelativeRVTest

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty

structure UnaryFieldwiseHypotheses where
  minusOne : L.Term Empty
  minusOne_realizes : minusOne.realize (Empty.elim : Empty → K) = -1
  fieldTerms : FieldTerms (convexLanguage L)
  fieldTerms_realize : letI := convexStructure O L; InterpretsFieldTerms (K := K) fieldTerms
  satCover : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P)
  satTests : ∀ (I : Type), Finite I → RealizesFinitelySatisfiableTypes 𝓜
    (CenterTestVariables S.carrier I) (CenterTestAssignments S.carrier I)
  satRows : ∀ d, let V := SumVariables P (RVVariables (Fin d))
    RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier V) (BaseAssignments S.carrier V)
  satLocal : ∀ (p : SortedAssignment Z P) d, let T := (𝓜).termGenerated (namedTuple S p)
    RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin d)))
      (BaseAssignments T.carrier (RVVariables (Fin d)))
  immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
    ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
      (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ r, e.toEmbedding .rv r = r

set_option maxHeartbeats 1100000 in
theorem unary_fieldwise_common_blowup_prepared_heads
    (hyp : UnaryFieldwiseHypotheses (L := L) O hO power S)
    (neg : rv O (-1) ∈ S.carrier .rv) (zero : S.carrier .rv) (hz : zero.val = 0)
    (A B : RetainedFieldFamily 𝓜 S 1 k) (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    (baseA : ∀ p u, appendAssignments p u ∈ A.fieldFiberTags idxA → p ∈ D)
    (baseB : ∀ p u, appendAssignments p u ∈ B.fieldFiberTags idxB → p ∈ D)
    (localCommon : ∀ p ∈ D, let T := (𝓜).termGenerated (namedTuple S p)
      let z := (𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl zero)
      let nT : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
      CommonBlowup (ElementaryClassStep O hO power T nT)
        ((A.atFieldTuple p).terminalGradedClass idxA z hz) ((B.atFieldTuple p).terminalGradedClass idxB z hz)) :
    ∃ (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B) (m n : ℕ)
      (orderA : Fin m ≃ H.target.tags) (orderB : Fin n ≃ J.target.tags),
      CommonBlowup (ElementaryClassStep O hO power S neg)
        (H.target.terminalGradedClass orderA zero hz) (J.target.terminalGradedClass orderB zero hz) := by
  obtain ⟨boundsA,vA⟩ := A.fieldFiberRows_exists_bounds idxA zero hyp.satRows
  obtain ⟨boundsB,vB⟩ := B.fieldFiberRows_exists_bounds idxB zero hyp.satRows
  let U := A.orderedFieldFiberRows idxA zero boundsA
  let V := B.orderedFieldFiberRows idxB zero boundsB
  let validA (p : SortedAssignment Z P) : Valid U zero p := fun i => vA _ p
  let validB (p : SortedAssignment Z P) : Valid V zero p := fun i => vB _ p
  have comp (p : SortedAssignment Z P) (hp : p ∈ D) :
      let T := (𝓜).termGenerated (namedTuple S p)
      let nT : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
      CommonBlowup (ElementaryClassStep O hO power T nT)
        (fiberClass U zero hz p (validA p)) (fiberClass V zero hz p (validB p)) := by
    intro T nT
    have rA : fiberClass U zero hz p (validA p) = _ := A.orderedFieldFiberRows_class idxA zero p hz boundsA (fun s => vA s p)
    have rB : fiberClass V zero hz p (validB p) = _ := B.orderedFieldFiberRows_class idxB zero p hz boundsB (fun s => vB s p)
    rw [rA,rB]
    exact localCommon p hp
  obtain ⟨C,pieces,cs,defPieces,pathValid,disj,cover,same⟩ :=
    uniform_prepared_blowup_paths O hO power S neg hyp.fieldTerms hyp.minusOne hyp.minusOne_realizes hyp.fieldTerms_realize
      hyp.satCover hyp.satTests hyp.immediate D defD zero hz (fun p _ => validA p) (fun p _ => validB p) (fun p _ => hyp.satLocal p) comp
  let line := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  have agreement (p p' : SortedAssignment Z P) (hp : p ∈ D) (eq : line.label (p .vf 0) = line.label (p' .vf 0)) :
      Agree (RelativeObjectFamily.tests U) p p' ∧ Agree (RelativeObjectFamily.tests V) p p' := by
    obtain ⟨i,_⟩ := Set.mem_iUnion.1 (cover ▸ hp)
    have tests := agree_append.1 (same i p p' eq).2
    exact ⟨i.val.left.tests_agree_at_source tests.1,i.val.right.tests_agree_at_source tests.2⟩
  have sameA := A.unaryCarrier_constant_of_rows idxA zero boundsA line D baseA (fun p p' hp eq => (agreement p p' hp eq).1)
  have sameB := B.unaryCarrier_constant_of_rows idxB zero boundsB line D baseB (fun p p' hp eq => (agreement p p' hp eq).2)
  let H := HeadContractionData.ofUnaryCenters O hO power S A cs hyp.minusOne hyp.minusOne_realizes hyp.fieldTerms hyp.fieldTerms_realize sameA
  let J := HeadContractionData.ofUnaryCenters O hO power S B cs hyp.minusOne hyp.minusOne_realizes hyp.fieldTerms hyp.fieldTerms_realize sameB
  let h := Fintype.card (HistoryIndex cs.length)
  let e : Fin h ≃ HistoryIndex cs.length := (Fintype.equivFin _).symm
  let codes := (Fintype.equivFin {i // i ∈ C}).symm
  have cover' : (⋃ i, pieces (codes i)) = D := by
    rw [← cover]
    exact Set.iUnion_congr_of_surjective _ codes.surjective (fun _ => rfl)
  obtain ⟨I₀,I₁,i₀,i₁,_,a₀,a₁,b₀,b₁,result⟩ :=
    prepared_blowup_comparison_of_cover O hO power S neg cs e hyp.fieldTerms hyp.minusOne hyp.minusOne_realizes hyp.fieldTerms_realize
      D defD (fun i => (codes i).val) (pieces ∘ codes) (fun i => defPieces (codes i))
      (fun _ _ ne => disj (codes.injective.ne ne)) cover' zero hz
      (fun i => pathValid (codes i)) (fun i => same (codes i))
  have zeroIndex : I₀.labels = {q ∈ preparedHistoryLabels O hO power S cs e D |
      q (e.symm (lastIndex cs.length)) ≠ 0 ↔ false = true} := by
    rw [i₀]
    ext q
    simp
  have nonzeroIndex : I₁.labels = {q ∈ preparedHistoryLabels O hO power S cs e D |
      q (e.symm (lastIndex cs.length)) ≠ 0 ↔ true = true} := by
    rw [i₁]
    ext q
    simp
  let tagsA := preparedHeadTagOrder O hO power S A idxA cs e
  let tagsB := preparedHeadTagOrder O hO power S B idxB cs e
  have zA := prepared_ordered_field_rows_gluedClass O hO power S A idxA cs e hyp.minusOne hyp.minusOne_realizes
    hyp.fieldTerms hyp.fieldTerms_realize D defD baseA sameA zero hz false boundsA I₀ zeroIndex a₀
  have nA := prepared_ordered_field_rows_gluedClass O hO power S A idxA cs e hyp.minusOne hyp.minusOne_realizes
    hyp.fieldTerms hyp.fieldTerms_realize D defD baseA sameA zero hz true boundsA I₁ nonzeroIndex a₁
  have zB := prepared_ordered_field_rows_gluedClass O hO power S B idxB cs e hyp.minusOne hyp.minusOne_realizes
    hyp.fieldTerms hyp.fieldTerms_realize D defD baseB sameB zero hz false boundsB I₀ zeroIndex b₀
  have nB := prepared_ordered_field_rows_gluedClass O hO power S B idxB cs e hyp.minusOne hyp.minusOne_realizes
    hyp.fieldTerms hyp.fieldTerms_realize D defD baseB sameB zero hz true boundsB I₁ nonzeroIndex b₁
  have allA := (congrArg₂ (· + ·) zA nA).trans (sum_extendTerminalSupport
    (fun s => objectClass 𝓜 S (H.target.terminalGradedPiece tagsA s zero hz)))
  have allB := (congrArg₂ (· + ·) zB nB).trans (sum_extendTerminalSupport
    (fun s => objectClass 𝓜 S (J.target.terminalGradedPiece tagsB s zero hz)))
  rw [allA,allB] at result
  exact ⟨H,J,h+a,h+b,tagsA,tagsB,result⟩

theorem unary_fieldwise_common_blowup {m n : ℕ}
    (hyp : UnaryFieldwiseHypotheses (L := L) O hO power S)
    (neg : rv O (-1) ∈ S.carrier .rv) (zero : S.carrier .rv) (hz : zero.val = 0)
    (A B : RetainedFieldFamily 𝓜 S 1 k) (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags)
    (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B)
    (tagsH : Fin m ≃ H.target.tags) (tagsJ : Fin n ≃ J.target.tags)
    (unaryA : ∀ C : HeadContractionData (n := 0) A, UnaryHeadComparisonHypotheses O hO power S H C)
    (unaryB : ∀ C : HeadContractionData (n := 0) B, UnaryHeadComparisonHypotheses O hO power S J C)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    (baseA : ∀ p u, appendAssignments p u ∈ A.fieldFiberTags idxA → p ∈ D)
    (baseB : ∀ p u, appendAssignments p u ∈ B.fieldFiberTags idxB → p ∈ D)
    (localCommon : ∀ p ∈ D, let T := (𝓜).termGenerated (namedTuple S p)
      let z := (𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl zero)
      let nT : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
      CommonBlowup (ElementaryClassStep O hO power T nT)
        ((A.atFieldTuple p).terminalGradedClass idxA z hz) ((B.atFieldTuple p).terminalGradedClass idxB z hz)) :
    CommonBlowup (ElementaryClassStep O hO power S neg)
      (H.target.terminalGradedClass tagsH zero hz) (J.target.terminalGradedClass tagsJ zero hz) := by
  obtain ⟨C,C',_,_,tagsC,tagsC',common⟩ := unary_fieldwise_common_blowup_prepared_heads O hO power S hyp neg zero hz
    A B idxA idxB D defD baseA baseB localCommon
  have l := unary_head_terminal_classes_common_blowup hO power S H C (unaryA C) neg zero hz tagsH tagsC
  have r := unary_head_terminal_classes_common_blowup hO power S J C' (unaryB C') neg zero hz tagsJ tagsC'
  have eq := commonBlowup_equivalence (ElementaryClassStep O hO power S neg)
    (elementaryClassStep_diamond O hO power S neg)
  exact eq.trans l (eq.trans common (eq.symm r))

end GeneralizedEuler.Section5
