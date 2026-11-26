module

public import Section5.RelativeBlowupPathDescent
public import Section5.PreparedUnaryRVIndex
public import Section5.GradedBlowupCongruence

/-! Entire local common-blowup paths descend across a prepared unary
base. Gluing uses the last leading term as one retained coordinate
and omits that coordinate on its zero stratum. -/

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

theorem prepared_common_blowup_glues_across_zero
    (cs : List (S.carrier .vf)) (e : Fin h ≃ HistoryIndex cs.length)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    {A : RelativeObjectFamily 𝓜 S P (Fin a)} {B : RelativeObjectFamily 𝓜 S P (Fin b)}
    (W : RelativeCommonBlowupScheme neg A B) (zero : S.carrier .rv) (hz : zero.val = 0)
    (valid : ∀ p ∈ D, W.valid zero p)
    (same : let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ p p' : SortedAssignment Z P, p ∈ D → p' ∈ D →
        T.label (p .vf 0) = T.label (p' .vf 0) → Agree W.tests p p') :
    let defH := preparedHistoryRelation_definable O hO power S cs e F minusOne hm hF defD
    let L := preparedHistoryLabels O hO power S cs e D
    let last := e.symm (lastIndex cs.length)
    let A' := fun i => (A i).descend defH
    let B' := fun j => (B j).descend defH
    ∃ (I₀ : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h 0)
      (I₁ : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h 1),
      I₀.labels = {p ∈ L | p last = 0} ∧ I₁.labels = {p ∈ L | p last ≠ 0} ∧ I₁.select 0 = last ∧
      ∃ (vA₀ : ∀ p ∈ I₀.labels, Valid A' zero (rvTupleAssignment p))
        (vA₁ : ∀ p ∈ I₁.labels, Valid A' zero (rvTupleAssignment p))
        (vB₀ : ∀ p ∈ I₀.labels, Valid B' zero (rvTupleAssignment p))
        (vB₁ : ∀ p ∈ I₁.labels, Valid B' zero (rvTupleAssignment p)),
        CommonBlowup (ElementaryClassStep O hO power S neg)
          (gluedClass zero hz I₀ A' vA₀+gluedClass zero hz I₁ A' vA₁)
          (gluedClass zero hz I₀ B' vB₀+gluedClass zero hz I₁ B' vB₁) := by
  intro defH L last A' B'
  let V := W.descend defH
  have all (q : Fin h → RV0 O) (hq : q ∈ L) : V.valid zero (rvTupleAssignment q) := by
    obtain ⟨p,hp,he⟩ := hq
    have x : preparedHistoryRelation O hO power S cs e D p (rvTupleAssignment q) := ⟨hp,he⟩
    exact W.descend_valid_of_tests defH x (fun p' hy => same p p' hp hy.1 (he.trans hy.2.symm)) zero (valid p hp)
  have defL := preparedHistoryLabels_definable O hO power S cs e F minusOne hm hF defD
  obtain ⟨I₀,eq₀⟩ := preparedHistoryLabels_zero_index O hO power S cs e defL
  obtain ⟨I₁,eq₁,sel⟩ := preparedHistoryLabels_nonzero_index O hO power S cs e defL
  have v₀ (p : Fin h → RV0 O) (hp : p ∈ I₀.labels) : V.valid zero (rvTupleAssignment p) :=
    all p (eq₀ ▸ hp).1
  have v₁ (p : Fin h → RV0 O) (hp : p ∈ I₁.labels) : V.valid zero (rvTupleAssignment p) :=
    all p (eq₁ ▸ hp).1
  refine ⟨I₀,I₁,eq₀,eq₁,sel,
    fun p hp => V.left.valid_source (v₀ p hp).1,
    fun p hp => V.left.valid_source (v₁ p hp).1,
    fun p hp => V.right.valid_source (v₀ p hp).2,
    fun p hp => V.right.valid_source (v₁ p hp).2,?_⟩
  exact graded_common_blowup_add O hO power S neg
    (V.glued_common_blowup I₀ zero hz v₀) (V.glued_common_blowup I₁ zero hz v₁)

end GeneralizedEuler.Section5
