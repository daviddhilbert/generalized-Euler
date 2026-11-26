module

public import Section5.UniformPreparedBlowupPaths
public import Section5.UniformRVBlowupGluing

/-! A single preparation makes all chosen paths descend to the same
history index. The pieces of that index cut the global graded class
and the common blowups on the pieces add. -/

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
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {h a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty
local notation "Q" => RVVariables (Fin h)
local notation "step" => ElementaryClassStep O hO power S neg

set_option maxHeartbeats 600000 in
theorem prepared_blowup_comparison_of_cover {J : Type} [Fintype J]
    (cs : List (S.carrier .vf)) (e : Fin h ≃ HistoryIndex cs.length)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    {A : RelativeObjectFamily 𝓜 S P (Fin a)} {B : RelativeObjectFamily 𝓜 S P (Fin b)}
    (W : J → RelativeCommonBlowupScheme neg A B)
    (pieces : J → Set (SortedAssignment Z P))
    (defPieces : ∀ j, SortedDefinableOver 𝓜 S.carrier (pieces j))
    (disj : Pairwise (fun i j => Disjoint (pieces i) (pieces j))) (cover : (⋃ j, pieces j) = D)
    (zero : S.carrier .rv) (hz : zero.val = 0)
    (valid : ∀ j p, p ∈ pieces j → (W j).valid zero p)
    (same : let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ j (p p' : SortedAssignment Z P), T.label (p .vf 0) = T.label (p' .vf 0) →
        (p ∈ pieces j ↔ p' ∈ pieces j) ∧ Agree (W j).tests p p') :
    let defH := preparedHistoryRelation_definable O hO power S cs e F minusOne hm hF defD
    let D' := preparedHistoryLabels O hO power S cs e D
    let last := e.symm (lastIndex cs.length)
    let A' := fun i => (A i).descend defH
    let B' := fun j => (B j).descend defH
    ∃ (I₀ : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h 0)
      (I₁ : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h 1),
      I₀.labels = {p ∈ D' | p last = 0} ∧ I₁.labels = {p ∈ D' | p last ≠ 0} ∧ I₁.select 0 = last ∧
      ∃ (vA₀ : ∀ p ∈ I₀.labels, Valid A' zero (rvTupleAssignment p))
        (vA₁ : ∀ p ∈ I₁.labels, Valid A' zero (rvTupleAssignment p))
        (vB₀ : ∀ p ∈ I₀.labels, Valid B' zero (rvTupleAssignment p))
        (vB₁ : ∀ p ∈ I₁.labels, Valid B' zero (rvTupleAssignment p)),
        CommonBlowup step (gluedClass zero hz I₀ A' vA₀+gluedClass zero hz I₁ A' vA₁)
          (gluedClass zero hz I₀ B' vB₀+gluedClass zero hz I₁ B' vB₁) := by
  intro defH D' last A' B'
  let C (j : J) := preparedHistoryLabels O hO power S cs e (pieces j)
  have defC (j : J) : isRVSet 𝓜 S (C j) :=
    preparedHistoryLabels_definable O hO power S cs e F minusOne hm hF (defPieces j)
  have coverC : D' ⊆ ⋃ j, C j := by
    rintro q ⟨p,hp,he⟩
    have mem : p ∈ ⋃ j, pieces j := cover ▸ hp
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 mem
    exact Set.mem_iUnion.2 ⟨j,p,hj,he⟩
  have disjointC : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j ne
    apply Set.disjoint_left.2
    rintro q ⟨p,hp,he⟩ ⟨p',hp',he'⟩
    exact Set.disjoint_left.1 (disj ne) ((same i p p' (he.trans he'.symm)).1.1 hp) hp'
  let named (j : J) := (W j).descend defH
  have v (j : J) (q : Fin h → RV0 O) (hq : q ∈ C j) : (named j).valid zero (rvTupleAssignment q) := by
    obtain ⟨p,hp,he⟩ := hq
    have pD : p ∈ D := cover ▸ Set.mem_iUnion.2 ⟨j,hp⟩
    have hr : preparedHistoryRelation O hO power S cs e D p (rvTupleAssignment q) := ⟨pD,he⟩
    exact (W j).descend_valid_of_tests defH hr (fun p' hp' => (same j p p' (he.trans hp'.2.symm)).2) zero (valid j p hp)
  have vA (q : Fin h → RV0 O) (hq : q ∈ D') : Valid A' zero (rvTupleAssignment q) := by
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 (coverC hq)
    exact (named j).left.valid_source (v j q hj).1
  have vB (q : Fin h → RV0 O) (hq : q ∈ D') : Valid B' zero (rvTupleAssignment q) := by
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 (coverC hq)
    exact (named j).right.valid_source (v j q hj).2
  have each (t : ℕ) (I : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h t) (sub : I.labels ⊆ D') :
      CommonBlowup step (gluedClass zero hz I A' (fun q hq => vA q (sub hq)))
        (gluedClass zero hz I B' (fun q hq => vB q (sub hq))) := by
    have cov : I.labels ⊆ ⋃ j, C j := sub.trans coverC
    rw [gluedClass_index_partition I A' zero hz _ C defC disjointC cov,
      gluedClass_index_partition I B' zero hz _ C defC disjointC cov]
    apply graded_common_blowup_sum O hO power S neg
    intro j
    exact (named j).glued_common_blowup (I.restrict (C j) (defC j)) zero hz (fun q hq => v j q hq.2)
  have defD' := preparedHistoryLabels_definable O hO power S cs e F minusOne hm hF defD
  obtain ⟨I₀,eq₀⟩ := preparedHistoryLabels_zero_index O hO power S cs e defD'
  obtain ⟨I₁,eq₁,sel⟩ := preparedHistoryLabels_nonzero_index O hO power S cs e defD'
  have sub₀ : I₀.labels ⊆ D' := eq₀ ▸ Set.inter_subset_left
  have sub₁ : I₁.labels ⊆ D' := eq₁ ▸ Set.inter_subset_left
  refine ⟨I₀,I₁,eq₀,eq₁,sel,
    fun q hq => vA q (sub₀ hq),fun q hq => vA q (sub₁ hq),
    fun q hq => vB q (sub₀ hq),fun q hq => vB q (sub₁ hq),?_⟩
  exact graded_common_blowup_add O hO power S neg (each 0 I₀ sub₀) (each 1 I₁ sub₁)

end GeneralizedEuler.Section5
