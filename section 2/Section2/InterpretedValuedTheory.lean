module

public import Section2.RecoveredValuedField
public import Section2.QuotientInterpretation

/-! First-order axioms for the representative interpretation of the
two-sorted expansion of a valued-field theory. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z

variable {L : Language.{u, v}} {E : Type w}
  {X : TCsort → Type z} (M : SortedStructure L E X)
  (I : QuotientInterpretation (convexLanguage L) L E) (minusOne : L.Term Empty)

/-- In the recovered interpretation every element is represented by a
field element, through identity on VF and the leading-term map on RV. -/
@[expose]
def representativeFromVF : ∀ s, X .vf → X s
  | .vf => id
  | .rv => M.rvMap

private def representByTerm {Var : TCsort → Type} (x : SortedTerm L E Var .vf) :
    ∀ s, SortedTerm L E Var s
  | .vf => x
  | .rv => rvOfVF x

private theorem realize_representByTerm {Var : TCsort → Type}
    (v : ∀ s, Var s → X s) (x : SortedTerm L E Var .vf) (s : TCsort) :
    (representByTerm x s).realize M v = representativeFromVF M s (x.realize M v) := by
  cases s
  · rfl
  · rw [representByTerm, rvOfVF, SortedTerm.realize, M.funMap_rv]
    rfl

private def iffSorted {Var : TCsort → Type} (p q : SortedFormula L E Var) :
    SortedFormula L E Var := (p.imp q).conjunction (q.imp p)

private theorem realize_iffSorted {Var : TCsort → Type} (p q : SortedFormula L E Var)
    (v : ∀ s, Var s → X s) :
    (iffSorted p q).realize M v ↔ (p.realize M v ↔ q.realize M v) := by
  rw [iffSorted, SortedFormula.realize_conjunction]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

private abbrev FieldBlock (n : ℕ) := AddSortedBlock (fun _ => Empty) .vf n

private def fieldBlockTerm {n : ℕ} (j : Fin n) : SortedTerm L E (FieldBlock n) .vf :=
  .var (.inr (j, ⟨rfl⟩))

private def formulaOnFieldBlock {A : Type} {n : ℕ} (φ : (convexLanguage L).Formula A)
    (name : A → Fin n) : SortedFormula L E (FieldBlock n) :=
  liftValuedFormula minusOne φ (Sum.elim (fieldBlockTerm ∘ name) Fin.elim0)

set_option linter.style.haveILetI false in
private theorem realize_formulaOnFieldBlock {A : Type} {n : ℕ}
    (φ : (convexLanguage L).Formula A) (name : A → Fin n) (x : Fin n → X .vf) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    (formulaOnFieldBlock (E := E) minusOne φ name).realize M
      (appendSortedBlock (fun _ => Empty.elim) x) ↔ φ.Realize (x ∘ name) := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  rw [formulaOnFieldBlock, realize_liftValuedFormula]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, fieldBlockTerm, SortedTerm.realize,
    appendSortedBlock]
  unfold Formula.Realize
  rw [Subsingleton.elim (default : Fin 0 → X .vf) (fun i => (Fin.elim0 i :
    SortedTerm L E (FieldBlock n) .vf).realize M (appendSortedBlock (fun _ => Empty.elim) x))]
  rfl

/-- The valuation-ring formula converts valued-field sentences into
two-sorted sentences. -/
def liftValuedSentence (φ : (convexLanguage L).Sentence) : SortedSentence L E :=
  liftValuedFormula minusOne φ (Sum.elim Empty.elim Fin.elim0)

set_option linter.style.haveILetI false in
theorem realize_liftValuedSentence (φ : (convexLanguage L).Sentence) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    (liftValuedSentence (E := E) minusOne φ).realize M ↔ φ.Realize (M := X .vf) := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  rw [SortedSentence.realize, liftValuedSentence, realize_liftValuedFormula]
  unfold Sentence.Realize Formula.Realize
  have hEmpty : (fun i : Empty => (Empty.elim i : SortedTerm L E (fun _ => Empty) .vf).realize M
      (fun _ => Empty.elim)) = (default : Empty → X .vf) := Subsingleton.elim _ _
  have hBound : (fun i : Fin 0 => (Fin.elim0 i : SortedTerm L E (fun _ => Empty) .vf).realize M
      (fun _ => Empty.elim)) = (default : Fin 0 → X .vf) := Subsingleton.elim _ _
  simp only [Sum.elim_inl, Sum.elim_inr, hEmpty, hBound]

/-- The leading-term quotient is surjective. -/
def rvSurjectiveAxiom : SortedSentence L E :=
  let eqRep :
      SortedFormula L E (AddSortedVar (AddSortedVar (fun _ => Empty) .rv) .vf) :=
    .equal (rvOfVF (.var (.inr ⟨rfl⟩))) (.var (.inl (.inr ⟨rfl⟩)))
  .all .rv (SortedFormula.all .vf eqRep.neg).neg

theorem realize_rvSurjectiveAxiom :
    (rvSurjectiveAxiom (L := L) (E := E)).realize M ↔ Function.Surjective M.rvMap := by
  classical
  simp only [SortedSentence.realize, rvSurjectiveAxiom, SortedFormula.realize_neg,
    SortedFormula.realize, not_forall, Classical.not_not, SortedTerm.realize, rvOfVF,
    M.funMap_rv, Fin.cases_zero, extendSortedAssignment, Function.Surjective]

/-- The interpreted equality formula says that representatives give
the same point of their sort. -/
def representativeEqualityAxiom (s : TCsort) : SortedSentence L E :=
  (iffSorted (formulaOnFieldBlock minusOne (I.equal s) id)
    (.equal (representByTerm (fieldBlockTerm 0) s) (representByTerm (fieldBlockTerm 1) s))).allBlock .vf 2

set_option linter.style.haveILetI false in
theorem realize_representativeEqualityAxiom (s : TCsort) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    (representativeEqualityAxiom I minusOne s).realize M ↔
      ∀ x : Fin 2 → X .vf, (I.equal s).Realize x ↔
        representativeFromVF M s (x 0) = representativeFromVF M s (x 1) := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  rw [SortedSentence.realize, representativeEqualityAxiom, SortedFormula.realize_allBlock]
  refine forall_congr' fun x => ?_
  rw [realize_iffSorted, realize_formulaOnFieldBlock, Function.comp_id, SortedFormula.realize,
    realize_representByTerm, realize_representByTerm]
  rfl

/-- One axiom relates an interpreted function graph to the named
sorted operation, on field representatives for all its arguments. -/
def representativeFunctionAxiom {ss : List TCsort} {s : TCsort}
    (f : FunctionSymbol L E ss s) : SortedSentence L E :=
  let names := (finSuccEquiv ss.length).symm
  let clause := iffSorted (formulaOnFieldBlock minusOne (I.function f) names)
    (.equal (representByTerm (fieldBlockTerm (names none)) s)
      (.app f (fun j => representByTerm (fieldBlockTerm (names (some j))) (ss.get j))))
  clause.allBlock .vf (ss.length + 1)

set_option linter.style.haveILetI false in
theorem realize_representativeFunctionAxiom {ss : List TCsort} {s : TCsort}
    (f : FunctionSymbol L E ss s) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    (representativeFunctionAxiom I minusOne f).realize M ↔
      ∀ x : Option (Fin ss.length) → X .vf, (I.function f).Realize x ↔
        representativeFromVF M s (x none) =
          M.funMap f (fun j => representativeFromVF M (ss.get j) (x (some j))) := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  rw [SortedSentence.realize, representativeFunctionAxiom, SortedFormula.realize_allBlock]
  let e := finSuccEquiv ss.length
  have h (x : Fin (ss.length + 1) → X .vf) :
      (iffSorted (formulaOnFieldBlock minusOne (I.function f) e.symm)
        (.equal (representByTerm (fieldBlockTerm (e.symm none)) s)
          (.app f (fun j => representByTerm (fieldBlockTerm (e.symm (some j))) (ss.get j))))).realize M
        (appendSortedBlock (fun _ => Empty.elim) x) ↔
      ((I.function f).Realize (x ∘ e.symm) ↔
        representativeFromVF M s ((x ∘ e.symm) none) =
          M.funMap f (fun j => representativeFromVF M (ss.get j) ((x ∘ e.symm) (some j)))) := by
    rw [realize_iffSorted, realize_formulaOnFieldBlock, SortedFormula.realize, realize_representByTerm,
      SortedTerm.realize]
    simp only [realize_representByTerm, fieldBlockTerm, SortedTerm.realize, appendSortedBlock,
      Function.comp_apply]
  constructor
  · intro hAll x
    have hx := (h (x ∘ e)).mp (hAll (x ∘ e))
    have he : (x ∘ e) ∘ e.symm = x := funext fun j => congrArg x (e.apply_symm_apply j)
    rwa [he] at hx
  · intro hAll x
    exact (h x).mpr (hAll (x ∘ e.symm))

/-- Relations in the sorted language agree with their formulas on
field representatives. -/
def representativeRelationAxiom {ss : List TCsort} (r : RelationSymbol L ss) : SortedSentence L E :=
  (iffSorted (formulaOnFieldBlock minusOne (I.relation r) id)
    (.rel r (fun j => representByTerm (fieldBlockTerm j) (ss.get j)))).allBlock .vf ss.length

set_option linter.style.haveILetI false in
theorem realize_representativeRelationAxiom {ss : List TCsort} (r : RelationSymbol L ss) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    (representativeRelationAxiom I minusOne r).realize M ↔
      ∀ x : Fin ss.length → X .vf, (I.relation r).Realize x ↔
        M.relMap r (fun j => representativeFromVF M (ss.get j) (x j)) := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  rw [SortedSentence.realize, representativeRelationAxiom, SortedFormula.realize_allBlock]
  refine forall_congr' fun x => ?_
  rw [realize_iffSorted, realize_formulaOnFieldBlock, Function.comp_id, SortedFormula.realize]
  simp only [realize_representByTerm, fieldBlockTerm, SortedTerm.realize, appendSortedBlock]

/-- The axioms are the valued-field theory, the surjectivity of RV, and
one representative clause for every equality, operation, and relation. -/
inductive InterpretedValuedAxiom (T : (convexLanguage L).Theory) :
    SortedSentence L E → Prop
  | valued (φ : (convexLanguage L).Sentence) (hφ : φ ∈ T) :
      InterpretedValuedAxiom T (liftValuedSentence minusOne φ)
  | surjective : InterpretedValuedAxiom T rvSurjectiveAxiom
  | equal (s : TCsort) : InterpretedValuedAxiom T (representativeEqualityAxiom I minusOne s)
  | operation {ss : List TCsort} {s : TCsort} (f : FunctionSymbol L E ss s) :
      InterpretedValuedAxiom T (representativeFunctionAxiom I minusOne f)
  | relation {ss : List TCsort} (r : RelationSymbol L ss) :
      InterpretedValuedAxiom T (representativeRelationAxiom I minusOne r)

def interpretedValuedTheory (T : (convexLanguage L).Theory) : SortedTheory L E :=
  {φ | InterpretedValuedAxiom I minusOne T φ}

set_option linter.style.haveILetI false in
/-- A model of the two-sorted axioms recovers a model of the valued
theory and realizes the given quotient interpretation. -/
theorem models_interpretedValuedTheory_iff (T : (convexLanguage L).Theory) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    (∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize M) ↔
      (X .vf ⊨ T) ∧ ∃ R : RealizesQuotientInterpretation I (A := X .vf) M,
        ∀ s x, R.rep s x = representativeFromVF M s x := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  constructor
  · intro h
    refine ⟨⟨fun φ hφ => (realize_liftValuedSentence M minusOne φ).mp (h _ (.valued φ hφ))⟩, ?_⟩
    refine ⟨{ rep := representativeFromVF M
              surjective := ?_
              equal := fun s => (realize_representativeEqualityAxiom M I minusOne s).mp (h _ (.equal s))
              function := fun f => (realize_representativeFunctionAxiom M I minusOne f).mp (h _ (.operation f))
              relation := fun r => (realize_representativeRelationAxiom M I minusOne r).mp (h _ (.relation r)) },
      fun s x => rfl⟩
    intro s
    cases s
    · exact Function.surjective_id
    · exact (realize_rvSurjectiveAxiom M).mp (h _ .surjective)
  · rintro ⟨hT, R, hR⟩ φ hφ
    letI := hT
    cases hφ with
    | valued ψ hψ => exact (realize_liftValuedSentence M minusOne ψ).mpr (Theory.realize_sentence_of_mem T hψ)
    | surjective =>
      apply (realize_rvSurjectiveAxiom M).mpr
      change Function.Surjective (representativeFromVF M .rv)
      exact (funext (hR .rv)) ▸ R.surjective .rv
    | equal s =>
      apply (realize_representativeEqualityAxiom M I minusOne s).mpr
      simpa only [← hR] using R.equal s
    | operation f =>
      apply (realize_representativeFunctionAxiom M I minusOne f).mpr
      simpa only [← hR] using R.function f
    | relation r =>
      apply (realize_representativeRelationAxiom M I minusOne r).mpr
      simpa only [← hR] using R.relation r

set_option linter.style.haveILetI false in
/-- The first-order theory of the interpreted expansion is complete
when the underlying valued-field theory is complete. -/
theorem interpretedValuedTheory_realize_iff_of_complete
    {T : (convexLanguage L).Theory} (hT : T.IsComplete)
    {Y : TCsort → Type*} (N : SortedStructure L E Y) [Nonempty (X .vf)] [Nonempty (Y .vf)]
    (hM : ∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize M)
    (hN : ∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize N) (φ : SortedSentence L E) :
    φ.realize M ↔ φ.realize N := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  letI := valuedStructureOfSorted N (recoveredRing N minusOne)
  obtain ⟨hMT, RM, _⟩ := (models_interpretedValuedTheory_iff M I minusOne T).mp hM
  obtain ⟨hNT, RN, _⟩ := (models_interpretedValuedTheory_iff N I minusOne T).mp hN
  letI := hMT
  letI := hNT
  exact sortedSentence_iff_of_complete_interpreted_theory I hT RM RN φ

section Canonical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : E → RV0 O → RV0 O)

set_option linter.style.haveILetI false in
/-- A canonical expansion models the interpreted theory when its
valuation-ring reduct models the field theory and the uniform formulas
realize its quotient interpretation. -/
theorem models_interpretedValuedTheory_canonical (T : (convexLanguage L).Theory)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1) :
    letI := convexStructure O L
    ∀ (_ : K ⊨ T)
      (R : RealizesQuotientInterpretation I (A := K) (canonicalStructure O hO P)),
      (∀ x, R.rep .vf x = x) → (∀ x, R.rep .rv x = rv O x) →
      ∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize (canonicalStructure O hO P) := by
  letI := convexStructure O L
  intro hT R hVF hRV
  apply (models_interpretedValuedTheory_iff (canonicalStructure O hO P) I minusOne T).mpr
  rw [recoveredValuedStructure_canonical_eq O hO P minusOne hm]
  refine ⟨hT, R, fun s x => ?_⟩
  cases s
  · exact hVF x
  · exact (hRV x).trans (canonicalStructure_rvMap O hO P x).symm

end Canonical

set_option linter.style.haveILetI false in
/-- Once the recovered field is given its valued-field data, every
model of the interpreted axioms has the canonical expansion up to an
isomorphism that fixes VF and sends the leading-term classes to the
classes of their original representatives. -/
theorem exists_canonicalIsomorphism_of_interpretedValuedModel
    [Field (X .vf)] [LinearOrder (X .vf)] [IsStrictOrderedRing (X .vf)] [L.Structure (X .vf)]
    (O : ValuationSubring (X .vf)) [L.Structure (Residue O)]
    (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O) (T : (convexLanguage L).Theory)
    (hRec : valuedStructureOfSorted M (recoveredRing M minusOne) = convexStructure O L)
    (hM : ∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize M) :
    letI := convexStructure O L
    ∀ (R : RealizesQuotientInterpretation I (A := X .vf) (canonicalStructure O hO P)),
      (∀ x, R.rep .vf x = x) → (∀ x, R.rep .rv x = rv O x) →
      ∃ e : SortedIsomorphism M (canonicalStructure O hO P),
        (∀ x, e.toEmbedding .vf x = x) ∧ ∀ x, e.toEmbedding .rv (M.rvMap x) = rv O x := by
  letI := convexStructure O L
  intro R hVF hRV
  let A := valuedStructureOfSorted M (recoveredRing M minusOne)
  letI := A
  obtain ⟨_, Rold, hold⟩ := (models_interpretedValuedTheory_iff M I minusOne T).mp hM
  have hCanonical :
      letI := valuedStructureOfSorted M (recoveredRing M minusOne)
      ∃ C : RealizesQuotientInterpretation I (A := X .vf) (canonicalStructure O hO P),
        (∀ x, C.rep .vf x = x) ∧ (∀ x, C.rep .rv x = rv O x) := by
    rw [hRec]
    exact ⟨R, hVF, hRV⟩
  obtain ⟨R', hVF', hRV'⟩ := hCanonical
  obtain ⟨e, he⟩ := exists_sortedIsomorphism_of_common_interpretation I Rold R'
  refine ⟨e, fun x => ?_, fun x => ?_⟩
  · have h := he .vf x
    rw [hold .vf x, hVF' x] at h
    exact h
  · have h := he .rv x
    rw [hold .rv x, hRV' x] at h
    exact h

end GeneralizedEuler.Section2
