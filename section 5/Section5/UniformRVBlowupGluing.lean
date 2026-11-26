module

public import Section5.RelativeIndexPartitions
public import Section5.RelativeBlowupPathSchemes
public import Section5.GradedBlowupCongruence

/-! Common blowups over the generated bases of an RV-indexed family
glue to a global common blowup, even if the local path lengths vary. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder RelativeObjectFamily

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {h t a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "Q" => RVVariables (Fin h)
local notation "step" => ElementaryClassStep O hO power S neg

theorem graded_common_blowup_sum {I : Type} [Fintype I] (A B : I → RVSemiring 𝓜 S)
    (localCommon : ∀ i, CommonBlowup step (A i) (B i)) :
    CommonBlowup step (∑ i, A i) (∑ i, B i) := by
  classical
  have each (D : Finset I) : CommonBlowup step (∑ i ∈ D, A i) (∑ i ∈ D, B i) := by
    induction D using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact ⟨0,0,0,rfl,rfl⟩
    | insert i D hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact graded_common_blowup_add O hO power S neg (localCommon i) ih
  exact each Finset.univ

set_option maxHeartbeats 600000 in
theorem uniform_rv_common_blowup_glues
    (D : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h t)
    {A : RelativeObjectFamily 𝓜 S Q (Fin a)} {B : RelativeObjectFamily 𝓜 S Q (Fin b)}
    (zero : S.carrier .rv) (hz : zero.val = 0)
    (vA : ∀ p ∈ D.labels, Valid A zero (rvTupleAssignment p))
    (vB : ∀ p ∈ D.labels, Valid B zero (rvTupleAssignment p))
    (satCover : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier Q) (BaseAssignments S.carrier Q))
    (satLocal : ∀ p ∈ D.labels, ∀ d, let T := (𝓜).termGenerated (namedTuple S (rvTupleAssignment p))
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin d)))
        (BaseAssignments T.carrier (RVVariables (Fin d))))
    (localCommon : ∀ p (hp : p ∈ D.labels),
      let q := rvTupleAssignment p
      let T := (𝓜).termGenerated (namedTuple S q)
      let nT : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S q) .rv (.inl ⟨_,neg⟩)).property
      CommonBlowup (ElementaryClassStep O hO power T nT)
        (fiberClass A zero hz q (vA p hp)) (fiberClass B zero hz q (vB p hp))) :
    CommonBlowup step (gluedClass zero hz D A vA) (gluedClass zero hz D B vB) := by
  let Base : Set (SortedAssignment Z Q) := {p | p .rv ∈ D.labels}
  have defBase : SortedDefinableOver 𝓜 S.carrier Base := D.definable
  have eta (p : SortedAssignment Z Q) : rvTupleAssignment (p .rv) = p := by
    funext s i
    cases s
    · exact i.elim
    · rfl
  have existsWitness (p : SortedAssignment Z Q) (hp : p ∈ Base) :
      ∃ W : RelativeCommonBlowupScheme neg A B, W.valid zero p :=
    eta p ▸ relative_common_blowup_scheme_of_classes (rvTupleAssignment (p .rv)) zero hz
      (satLocal (p .rv) hp) (vA (p .rv) hp) (vB (p .rv) hp) (localCommon (p .rv) hp)
  obtain ⟨covers,pieces,defPieces,valid,disj,cover⟩ :=
    uniform_relative_common_blowup_schemes satCover zero Base defBase existsWitness
  let J := {w // w ∈ covers}
  let e := (Fintype.equivFin J).symm
  let P (i : Fin (Fintype.card J)) : Set (Fin h → RV0 O) := {p | rvTupleAssignment p ∈ pieces (e i)}
  have defP (i : Fin (Fintype.card J)) : isRVSet 𝓜 S (P i) := by
    change SortedDefinableOver 𝓜 S.carrier {p : SortedAssignment Z Q | rvTupleAssignment (p .rv) ∈ pieces (e i)}
    have eq : {p : SortedAssignment Z Q | rvTupleAssignment (p .rv) ∈ pieces (e i)} = pieces (e i) :=
      Set.ext (fun p => (congrArg (· ∈ pieces (e i)) (eta p)).to_iff)
    rw [eq]
    exact defPieces (e i)
  have disjoint : Pairwise (fun i j => Disjoint (P i) (P j)) :=
    fun i j ne => Set.disjoint_left.2 (fun _ hi hj => Set.disjoint_left.1 (disj (e.injective.ne ne)) hi hj)
  have exhaustive : D.labels ⊆ ⋃ j, P j := by
    intro p hp
    have m : rvTupleAssignment p ∈ Base := hp
    rw [← cover] at m
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 m
    refine Set.mem_iUnion.2 ⟨e.symm j,?_⟩
    change rvTupleAssignment p ∈ pieces (e (e.symm j))
    rwa [e.apply_symm_apply]
  rw [gluedClass_index_partition D A zero hz vA P defP disjoint exhaustive,
    gluedClass_index_partition D B zero hz vB P defP disjoint exhaustive]
  apply graded_common_blowup_sum O hO power S neg
  intro j
  let Dj := D.restrict (P j) (defP j)
  exact (e j).val.glued_common_blowup Dj zero hz (fun _ hp => valid (e j) _ hp.2)

end GeneralizedEuler.Section5
