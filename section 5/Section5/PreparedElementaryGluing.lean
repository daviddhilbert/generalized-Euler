module

public import Section5.RelativeElementaryPreparation

/-! On a prepared unary base, one relative elementary scheme descends
to both leading-term strata and gives one global elementary step on
each. The degree of the retained leading term is omitted at zero. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {h k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty
local notation "Q" => RVVariables (Fin h)

theorem prepared_elementary_scheme_valid
    (cs : List (S.carrier .vf)) (e : Fin h ≃ HistoryIndex cs.length)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    (W : RelativeElementaryScheme 𝓜 S P k)
    (zero : S.carrier .rv) (valid : ∀ p ∈ D, W.valid zero p)
    (same : let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ p p' : SortedAssignment Z P, T.label (p .vf 0) = T.label (p' .vf 0) →
        (∀ a, appendAssignments p a ∈ W.tags ↔ appendAssignments p' a ∈ W.tags) ∧
        (∀ a b, appendAssignments (appendAssignments p a) b ∈ W.graph ↔
          appendAssignments (appendAssignments p' a) b ∈ W.graph)) :
    let defH := preparedHistoryRelation_definable O hO power S cs e F minusOne hm hF defD
    ∀ q ∈ preparedHistoryLabels O hO power S cs e D, (W.descend defH).valid zero (rvTupleAssignment q) := by
  intro defH q hq
  obtain ⟨p,hp,ep⟩ := hq
  have h : preparedHistoryRelation O hO power S cs e D p (rvTupleAssignment q) := ⟨hp,ep⟩
  have equate (p' : SortedAssignment Z P) (h' : preparedHistoryRelation O hO power S cs e D p' (rvTupleAssignment q)) :=
    same p p' (h.2.trans h'.2.symm)
  exact W.descend_valid defH h zero (fun p' h' => (equate p' h').1) (fun p' h' => (equate p' h').2) (valid p hp)

theorem prepared_elementary_glues_across_zero
    (cs : List (S.carrier .vf)) (e : Fin h ≃ HistoryIndex cs.length)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    (W : RelativeElementaryScheme 𝓜 S P k) (zero : S.carrier .rv) (hzero : zero.val = 0)
    (neg : rv O (-1) ∈ S.carrier .rv)
    (valid : ∀ p ∈ D, W.valid zero p)
    (same : let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ p p' : SortedAssignment Z P, T.label (p .vf 0) = T.label (p' .vf 0) →
        (∀ a, appendAssignments p a ∈ W.tags ↔ appendAssignments p' a ∈ W.tags) ∧
        (∀ a b, appendAssignments (appendAssignments p a) b ∈ W.graph ↔
          appendAssignments (appendAssignments p' a) b ∈ W.graph)) :
    let defH := preparedHistoryRelation_definable O hO power S cs e F minusOne hm hF defD
    let V := W.descend defH
    let B := preparedHistoryLabels O hO power S cs e D
    let j := e.symm (lastIndex cs.length)
    ∃ (I₀ : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h 0)
      (I₁ : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h 1),
      I₀.labels = {p ∈ B | p j = 0} ∧ I₁.labels = {p ∈ B | p j ≠ 0} ∧ I₁.select 0 = j ∧
      ∃ (v₀ : ∀ p ∈ I₀.labels, V.valid zero (rvTupleAssignment p))
        (v₁ : ∀ p ∈ I₁.labels, V.valid zero (rvTupleAssignment p)),
        let A₀ := V.row I₀ zero hzero v₀
        let A₁ := V.row I₁ zero hzero v₁
        let f₀ := V.row_deleted_bound I₀ zero hzero v₀
        let f₁ := V.row_deleted_bound I₁ zero hzero v₁
        let x₀ := (A₀.lowerRow V.slot f₀).gluedClass + (RelativeRVRow.upperRow O hO power S neg A₀ V.slot f₀).gluedClass
        let x₁ := (A₁.lowerRow V.slot f₁).gluedClass + (RelativeRVRow.upperRow O hO power S neg A₁ V.slot f₁).gluedClass
        BlowupSteps (ElementaryClassStep O hO power S neg) 2 (A₀.gluedClass + A₁.gluedClass) (x₀ + x₁) := by
  intro defH V B j
  have defB := preparedHistoryLabels_definable O hO power S cs e F minusOne hm hF defD
  have all := prepared_elementary_scheme_valid O hO power S cs e F minusOne hm hF D defD W zero valid same
  obtain ⟨I₀,eq₀⟩ := preparedHistoryLabels_zero_index O hO power S cs e defB
  obtain ⟨I₁,eq₁,select⟩ := preparedHistoryLabels_nonzero_index O hO power S cs e defB
  have v₀ : ∀ p ∈ I₀.labels, V.valid zero (rvTupleAssignment p) := fun p hp => all p (eq₀ ▸ hp).1
  have v₁ : ∀ p ∈ I₁.labels, V.valid zero (rvTupleAssignment p) := fun p hp => all p (eq₁ ▸ hp).1
  refine ⟨I₀,I₁,eq₀,eq₁,select,v₀,v₁,?_⟩
  intro A₀ A₁ f₀ f₁ x₀ x₁
  have s₀ : ElementaryClassStep O hO power S neg A₀.gluedClass x₀ :=
    relative_elementary_scheme_glued_step O hO power S neg V I₀ zero hzero v₀
  have s₁ : ElementaryClassStep O hO power S neg A₁.gluedClass x₁ :=
    relative_elementary_scheme_glued_step O hO power S neg V I₁ zero hzero v₁
  refine ⟨x₀ + A₁.gluedClass,elementaryClassStep_add O hO power S neg s₀ A₁.gluedClass,x₀+x₁,?_,rfl⟩
  simpa only [add_comm x₀] using elementaryClassStep_add O hO power S neg s₁ x₀

end GeneralizedEuler.Section5
