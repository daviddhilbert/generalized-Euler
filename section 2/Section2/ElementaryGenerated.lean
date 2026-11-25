module

public import Section2.RVMonomials
public import Section2.SortedQE

/-! Nontrivial valuation in the elementarity criterion after Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w a

variable {L : Language.{u, v}} {E : Type w}
  {K : Type (max u v w a)} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

private abbrev NoVariables : TCsort → Type a := fun _ => PEmpty

private def noAssignment {M : TCsort → Type*} : ∀ s, NoVariables.{a} s → M s :=
  fun _ i => PEmpty.elim i

private def nontrivialValueWitness : SortedFormula L E (AddSortedVar (NoVariables.{a}) .rv) :=
  let t : SortedTerm L E (AddSortedVar (NoVariables.{a}) .rv) .rv := .var (.inr ⟨rfl⟩)
  (.equal t rvZeroTerm : SortedFormula L E _).neg.conjunction
    (rvSameUnsignedValueFormula t rvOneTerm).neg

private theorem nontrivialValueWitness_isQF :
    (nontrivialValueWitness.{u, v, w, a} (L := L) (E := E)).IsQF := by
  apply SortedFormula.conjunction_isQF
  · exact SortedFormula.neg_isQF (.equal _ _)
  · exact SortedFormula.neg_isQF (rvSameUnsignedValueFormula_isQF _ _)

private theorem realize_nontrivialValueWitness (t : RV0 O) :
    (nontrivialValueWitness.{u, v, w, a} (L := L) (E := E)).realize
      (canonicalStructure O hO P)
      (extendSortedAssignment noAssignment t) ↔ t ≠ 0 ∧ unsignedValue O t ≠ 1 := by
  simp only [nontrivialValueWitness, SortedFormula.realize_conjunction, SortedFormula.realize_neg,
    SortedFormula.realize, realize_rvZeroTerm, realize_rvSameUnsignedValueFormula O hO P,
    SortedTerm.realize, extendSortedAssignment, rvOneTerm]
  change (t ≠ 0 ∧ unsignedValue O t ≠ unsignedValue O (1 : RV0 O)) ↔ _
  rw [map_one]

/-- Corollary 2.17. A VF-generated substructure is elementary exactly
when its valuation is nontrivial. The proper-pair input takes a
VF-generated substructure with nontrivial valuation to a model of the
sorted theory. -/
theorem elementary_iff_nontrivial_of_vfGenerated
    (T : SortedTheory L E)
    (hQE : ∀ {Var : TCsort → Type a} (φ : SortedFormula L E Var), ∃ ψ, ψ.IsQF ∧
      ∀ M : T.PointedModel Var, M.realizes φ ↔ M.realizes ψ)
    (hM : ∀ ψ ∈ T, ψ.realize (canonicalStructure O hO P))
    (hVal : O.valuation.IsNontrivial)
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (hS : ∀ s, Nonempty (S.carrier s))
    (hGen : S.structureOn.IsVFGenerated)
    (hProper : S.structureOn.IsVFGenerated →
      (∃ t : S.carrier .rv, t.val ≠ 0 ∧ unsignedValue O t.val ≠ 1) →
      ∀ ψ ∈ T, ψ.realize S.structureOn) :
    (∀ {Var : TCsort → Type a} (φ : SortedFormula L E Var) (x : ∀ s, Var s → S.carrier s),
      φ.realize S.structureOn x ↔
        φ.realize (canonicalStructure O hO P) (fun s i => (x s i).val)) ↔
      ∃ t : S.carrier .rv, t.val ≠ 0 ∧ unsignedValue O t.val ≠ 1 := by
  classical
  let M := canonicalStructure (L := L) O hO P
  constructor
  · intro hElem
    let φ : SortedFormula L E (NoVariables.{a}) :=
      (SortedFormula.all .rv (nontrivialValueWitness.{u, v, w, a} (L := L) (E := E)).neg).neg
    let e : ∀ s, NoVariables.{a} s → S.carrier s := noAssignment
    obtain ⟨x, hx₀, hx₁⟩ := (Valuation.isNontrivial_iff_exists_lt_one O.valuation).mp hVal
    have hSat : φ.realize M (fun s i => (e s i).val) := by
      simp only [φ, SortedFormula.realize_neg, SortedFormula.realize, not_forall, not_not]
      refine ⟨rv O x, ?_⟩
      have he : (fun s (i : NoVariables.{a} s) => (e s i).val) =
          (noAssignment : ∀ s, NoVariables.{a} s → CanonicalSort O s) := funext fun _ => funext fun i => i.elim
      rw [he, realize_nontrivialValueWitness.{u, v, w, a} (L := L) O hO P]
      exact ⟨(rv_eq_zero_iff O).not.mpr hx₀, by rw [unsignedValue_rv]; exact hx₁.ne⟩
    have h := (hElem φ e).mpr hSat
    simp only [φ, SortedFormula.realize_neg, SortedFormula.realize, not_forall, not_not] at h
    obtain ⟨t, ht⟩ := h
    refine ⟨t, (realize_nontrivialValueWitness.{u, v, w, a} (L := L) O hO P t.val).mp ?_⟩
    have hi := S.inclusion.realize_qf (nontrivialValueWitness_isQF.{u, v, w, a} (L := L) (E := E))
      (extendSortedAssignment e t)
    have hArgs : S.inclusion.mapAssignment (extendSortedAssignment e t) =
        extendSortedAssignment noAssignment t.val := by
      funext s i
      rw [SortedEmbedding.mapAssignment_apply, SortedSubstructure.inclusion_apply]
      cases i with
      | inl i => exact i.elim
      | inr i =>
        obtain rfl := i.down
        rfl
    rw [hArgs] at hi
    exact hi.mpr ht
  · intro hProperS Var φ x
    obtain ⟨ψ, hqf, hEq⟩ := hQE φ
    let m : T.PointedModel Var :=
      ⟨CanonicalSort O, M, fun s i => (x s i).val,
        fun s => by cases s <;> exact ⟨0⟩, hM⟩
    have hs : ∀ θ ∈ T, θ.realize S.structureOn := hProper hGen hProperS
    let n : T.PointedModel Var := ⟨(fun s => S.carrier s), S.structureOn, x, hS, hs⟩
    have h := S.inclusion.realize_qf hqf x
    have he : S.inclusion.mapAssignment x = fun s i => (x s i).val := by
      funext s i
      rw [SortedEmbedding.mapAssignment_apply, SortedSubstructure.inclusion_apply]
    rw [he] at h
    exact (hEq n).trans (h.symm.trans (hEq m).symm)

end GeneralizedEuler.Section2
