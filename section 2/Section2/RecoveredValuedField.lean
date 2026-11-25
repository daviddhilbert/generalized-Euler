module

public import Section2.RVMonomials
public import Section2.ValuedFieldFormulas
public import Section2.SortedQuantifierBlock

/-! Interpret the valued-field reduct inside the two-sorted language.
The valuation ring is recovered by signed bounds and the residue-unit
predicate, as in the proof of Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z a b

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {Var : TCsort → Type a}

/-- The VF-symbol interpretations of a two-sorted structure, together
with a chosen interpretation of the extra valuation-ring predicate. -/
@[expose, instance_reducible]
def valuedStructureOfSorted (M : SortedStructure L E X) (ring : Set (X .vf)) :
    (convexLanguage L).Structure (X .vf) where
  funMap
    | .inl f, x => M.funMap (.vf f) (expandHomogeneousArgs x)
    | .inr f, _ => f.elim
  RelMap
    | .inl r, x => M.relMap (.vf r) (expandHomogeneousArgs x)
    | .inr .mem, x => x 0 ∈ ring

variable {α : Type b}

/-- Field terms of the valued-field language use only the VF symbols. -/
def liftValuedTerm (names : α → SortedTerm L E Var .vf) :
    (convexLanguage L).Term α → SortedTerm L E Var .vf
  | .var i => names i
  | .func (.inl f) args =>
      .app (.vf f) (expandHomogeneousArgs (fun i => liftValuedTerm names (args i)))
  | .func (.inr f) _ => f.elim

private theorem realize_expandedTerms (M : SortedStructure L E X)
    (v : ∀ s, Var s → X s) {n : ℕ} (ts : Fin n → SortedTerm L E Var .vf) :
    (fun j => (expandHomogeneousArgs ts j).realize M v) =
      expandHomogeneousArgs (fun i => (ts i).realize M v) := by
  exact expandHomogeneousArgs_map (fun s (t : SortedTerm L E Var s) => t.realize M v) ts

set_option linter.style.haveILetI false in
theorem realize_liftValuedTerm (M : SortedStructure L E X) (ring : Set (X .vf))
    (names : α → SortedTerm L E Var .vf) (t : (convexLanguage L).Term α)
    (v : ∀ s, Var s → X s) :
    letI := valuedStructureOfSorted M ring
    (liftValuedTerm names t).realize M v = t.realize (fun i => (names i).realize M v) := by
  letI := valuedStructureOfSorted M ring
  induction t with
  | var => rfl
  | func f ts ih =>
    cases f with
    | inl f =>
      rw [liftValuedTerm, SortedTerm.realize, realize_expandedTerms M v]
      change M.funMap (.vf f) (expandHomogeneousArgs
          (fun i => (liftValuedTerm names (ts i)).realize M v)) =
        M.funMap (.vf f) (expandHomogeneousArgs (fun i => (ts i).realize
          (fun j => (names j).realize M v)))
      exact congrArg (fun x => M.funMap (.vf f) (expandHomogeneousArgs x)) (funext ih)
    | inr f => exact f.elim

@[expose]
def rvOfVF (x : SortedTerm L E Var .vf) : SortedTerm L E Var .rv :=
  .app .rv (Fin.cases x (fun i => i.elim0))

private def rvArgs {Y : TCsort → Type*} (x y : Y .rv) : SortedArgs Y [.rv, .rv] :=
  Fin.cases x (Fin.cases y (fun i => i.elim0))

private def rvLE (x y : SortedTerm L E Var .rv) : SortedFormula L E Var :=
  .rel .rvLE (rvArgs x y)

private def residueUnit (x : SortedTerm L E Var .rv) : SortedFormula L E Var :=
  .rel .residueNonzero (Fin.cases x (fun i => i.elim0))

/-- On VF, membership in the valuation ring is recognized by the
signed RV bounds or the residue-unit test. -/
def recoveredRingFormula (minusOne : L.Term Empty) (x : SortedTerm L E Var .vf) :
    SortedFormula L E Var :=
  let lo := rvOfVF (liftValuedTerm Empty.elim ((LHom.sumInl : L →ᴸ convexLanguage L).onTerm minusOne))
  ((rvLE lo (rvOfVF x)).conjunction (rvLE (rvOfVF x) rvOneTerm)).disjunction
    (residueUnit (rvOfVF x))

theorem recoveredRingFormula_isQF (minusOne : L.Term Empty) (x : SortedTerm L E Var .vf) :
    (recoveredRingFormula minusOne x).IsQF :=
  SortedFormula.disjunction_isQF (SortedFormula.conjunction_isQF (.rel .rvLE _) (.rel .rvLE _))
    (.rel .residueNonzero _)

/-- The valuation-ring predicate obtained from the two-sorted
operations, before assuming the structure comes from a valued field. -/
def recoveredRing (M : SortedStructure L E X) (minusOne : L.Term Empty) : Set (X .vf) :=
  letI := valuedStructureOfSorted M ∅
  let minusOneVF := ((LHom.sumInl : L →ᴸ convexLanguage L).onTerm minusOne).realize Empty.elim
  let rv₀ := M.funMap .rvOne (fun i => i.elim0)
  {x | (M.relMap .rvLE (rvArgs (M.rvMap minusOneVF) (M.rvMap x)) ∧
    M.relMap .rvLE (rvArgs (M.rvMap x) rv₀)) ∨
      M.relMap .residueNonzero (Fin.cases (M.rvMap x) (fun i => i.elim0))}

theorem realize_recoveredRingFormula (M : SortedStructure L E X) (minusOne : L.Term Empty)
    (x : SortedTerm L E Var .vf) (v : ∀ s, Var s → X s) :
    (recoveredRingFormula minusOne x).realize M v ↔ x.realize M v ∈ recoveredRing M minusOne := by
  let V := valuedStructureOfSorted M ∅
  let t := (LHom.sumInl : L →ᴸ convexLanguage L).onTerm minusOne
  have hterm := realize_liftValuedTerm M ∅ (Var := Var) Empty.elim t v
  have hminus : (liftValuedTerm (Var := Var) Empty.elim
      ((LHom.sumInl : L →ᴸ convexLanguage L).onTerm minusOne)).realize M v =
        @Term.realize (convexLanguage L) (X .vf) V Empty Empty.elim t := by
    rw [hterm, Subsingleton.elim (fun i : Empty =>
      (Empty.elim i : SortedTerm L E Var .vf).realize M v) (Empty.elim : Empty → X .vf)]
  rw [recoveredRingFormula, SortedFormula.realize_disjunction, SortedFormula.realize_conjunction]
  unfold recoveredRing
  let oneRV := M.funMap .rvOne (fun i => i.elim0)
  have hOne : (rvOneTerm : SortedTerm L E Var .rv).realize M v = oneRV := by
    rw [rvOneTerm, SortedTerm.realize]
    congr 1
    funext i
    exact i.elim0
  have hRV (y : SortedTerm L E Var .vf) : (rvOfVF y).realize M v = M.rvMap (y.realize M v) := by
    rw [rvOfVF, SortedTerm.realize, M.funMap_rv]
    rfl
  have hLE (p q : SortedTerm L E Var .rv) :
      (rvLE p q).realize M v =
        M.relMap .rvLE (rvArgs (p.realize M v) (q.realize M v)) := by
    unfold rvLE
    rw [SortedFormula.realize]
    congr 1
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => i.elim0)) j <;> rfl
  have hu (p : SortedTerm L E Var .rv) :
      (residueUnit p).realize M v = M.relMap .residueNonzero (Fin.cases (p.realize M v) (fun i => i.elim0)) := by
    unfold residueUnit
    rw [SortedFormula.realize]
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => i.elim0) j
    rfl
  simp only [hLE, hu, hRV, hOne, hminus]
  rfl

private def extendVFNames {n : ℕ} (names : α ⊕ Fin n → SortedTerm L E Var .vf) :
    α ⊕ Fin (n + 1) → SortedTerm L E (AddSortedVar Var .vf) .vf
  | .inl i => (names (.inl i)).relabel (fun _ => Sum.inl)
  | .inr j => Fin.lastCases (.var (.inr ⟨rfl⟩))
      (fun i => (names (.inr i)).relabel (fun _ => Sum.inl)) j

/-- Interpret the valued-field syntax in the two-sorted language,
relativizing every field quantifier to VF and using the ring test. -/
def liftValuedFormula (minusOne : L.Term Empty) :
    {V : TCsort → Type a} → {n : ℕ} → (convexLanguage L).BoundedFormula α n →
      (α ⊕ Fin n → SortedTerm L E V .vf) → SortedFormula L E V
  | _, _, .falsum, _ => .falsum
  | _, _, .equal x y, names => .equal (liftValuedTerm names x) (liftValuedTerm names y)
  | _, _, .rel (.inl r) ts, names =>
      .rel (.vf r) (expandHomogeneousArgs (fun i => liftValuedTerm names (ts i)))
  | _, _, .rel (.inr .mem) ts, names => recoveredRingFormula minusOne (liftValuedTerm names (ts 0))
  | _, _, .imp φ ψ, names => .imp (liftValuedFormula minusOne φ names) (liftValuedFormula minusOne ψ names)
  | _, _, .all φ, names => .all .vf (liftValuedFormula minusOne φ (extendVFNames names))

set_option linter.style.haveILetI false in
theorem realize_liftValuedFormula (M : SortedStructure L E X) (minusOne : L.Term Empty)
    {n : ℕ} (φ : (convexLanguage L).BoundedFormula α n)
    (names : α ⊕ Fin n → SortedTerm L E Var .vf) (v : ∀ s, Var s → X s) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    (liftValuedFormula minusOne φ names).realize M v ↔
      φ.Realize (fun i => (names (.inl i)).realize M v) (fun i => (names (.inr i)).realize M v) := by
  let R := recoveredRing M minusOne
  letI := valuedStructureOfSorted M R
  induction φ generalizing Var with
  | falsum => rfl
  | equal x y =>
    rw [liftValuedFormula, SortedFormula.realize, realize_liftValuedTerm M R, realize_liftValuedTerm M R]
    have hAssign : (fun i => (names i).realize M v) =
        Sum.elim (fun i => (names (.inl i)).realize M v) (fun i => (names (.inr i)).realize M v) := by
      funext i
      cases i <;> rfl
    rw [hAssign]
    rfl
  | rel r ts =>
    have hAssign : (fun i => (names i).realize M v) =
        Sum.elim (fun i => (names (.inl i)).realize M v) (fun i => (names (.inr i)).realize M v) := by
      funext i
      cases i <;> rfl
    cases r with
    | inl r =>
      rw [liftValuedFormula, SortedFormula.realize, realize_expandedTerms]
      change M.relMap (.vf r) (expandHomogeneousArgs (fun i => (liftValuedTerm names (ts i)).realize M v)) ↔
        M.relMap (.vf r) (expandHomogeneousArgs (fun i => (ts i).realize (Sum.elim _ _)))
      have he : (fun i => (liftValuedTerm names (ts i)).realize M v) =
          (fun i => (ts i).realize (Sum.elim
            (fun j => (names (.inl j)).realize M v) (fun j => (names (.inr j)).realize M v))) := by
        funext j
        rw [realize_liftValuedTerm M R, hAssign]
      rw [he]
    | inr r =>
      cases r
      rw [liftValuedFormula, realize_recoveredRingFormula, realize_liftValuedTerm M R, hAssign]
      rfl
  | imp φ ψ ihφ ihψ =>
    exact (ihφ names v).imp (ihψ names v)
  | @all n φ ih =>
    change (∀ y : X .vf, (liftValuedFormula minusOne φ (extendVFNames names)).realize M
        (extendSortedAssignment v y)) ↔
      ∀ y : X .vf, φ.Realize (fun i => (names (.inl i)).realize M v)
        (Fin.snoc (fun i => (names (.inr i)).realize M v) y)
    refine forall_congr' fun y => (ih _ _).trans ?_
    have hFree (i : α) :
        ((extendVFNames names) (.inl i)).realize M (extendSortedAssignment v y) =
          (names (.inl i)).realize M v := by
      simp only [extendVFNames, SortedTerm.realize_relabel, Function.comp_def, extendSortedAssignment]
    have hBound : (fun j => ((extendVFNames names) (.inr j)).realize M (extendSortedAssignment v y)) =
        Fin.snoc (fun j => (names (.inr j)).realize M v) y := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [extendVFNames, Fin.lastCases_last, SortedTerm.realize,
          extendSortedAssignment, Fin.snoc_last]
      · simp only [extendVFNames, Fin.lastCases_castSucc, Fin.snoc_castSucc,
          SortedTerm.realize_relabel, Function.comp_def, extendSortedAssignment]
    rw [funext hFree, hBound]

set_option linter.style.haveILetI false in
/-- Restricting a sorted embedding to VF is an embedding of the
recovered valued fields, since the valuation-ring test is quantifier-free. -/
def valuedEmbeddingOfSorted {Y : TCsort → Type*} {M : SortedStructure L E X}
    {N : SortedStructure L E Y} (e : SortedEmbedding M N) (minusOne : L.Term Empty) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    letI := valuedStructureOfSorted N (recoveredRing N minusOne)
    X .vf ↪[convexLanguage L] Y .vf := by
  letI := valuedStructureOfSorted M (recoveredRing M minusOne)
  letI := valuedStructureOfSorted N (recoveredRing N minusOne)
  refine { toFun := e.toEmbedding .vf, inj' := (e.toEmbedding .vf).injective
           map_fun' := ?_, map_rel' := ?_ }
  · intro n f x
    cases f with
    | inl f =>
      have h := e.map_fun (.vf f) (expandHomogeneousArgs x)
      rw [expandHomogeneousArgs_map (s := .vf) (fun s (a : X s) => e.toEmbedding s a) x] at h
      exact h
    | inr f => exact f.elim
  · intro n r x
    cases r with
    | inl r =>
      have h := e.map_rel (.vf r) (expandHomogeneousArgs x)
      rw [expandHomogeneousArgs_map (s := .vf) (fun s (a : X s) => e.toEmbedding s a) x] at h
      exact h
    | inr r =>
      cases r
      let W : TCsort → Type := fun s => match s with | .vf => Unit | .rv => PEmpty
      let v (s : TCsort) : W s → X s := match s with
        | .vf => fun _ => x 0
        | .rv => PEmpty.elim
      let term : SortedTerm L E W .vf := .var ()
      have h := e.realize_qf (recoveredRingFormula_isQF minusOne term) v
      rw [realize_recoveredRingFormula, realize_recoveredRingFormula] at h
      change (e.toEmbedding .vf (x 0) ∈ recoveredRing N minusOne ↔
        x 0 ∈ recoveredRing M minusOne)
      simpa only [term, SortedTerm.realize, SortedEmbedding.mapAssignment_apply, v] using h

theorem valuedEmbeddingOfSorted_apply {Y : TCsort → Type*} {M : SortedStructure L E X}
    {N : SortedStructure L E Y} (e : SortedEmbedding M N) (minusOne : L.Term Empty) (x : X .vf) :
    letI := valuedStructureOfSorted M (recoveredRing M minusOne)
    letI := valuedStructureOfSorted N (recoveredRing N minusOne)
    valuedEmbeddingOfSorted e minusOne x = e.toEmbedding .vf x := by rfl

section Canonical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

set_option linter.style.haveILetI false in
private theorem valuedStructureOfSorted_expansion (R : Set K) :
    letI := valuedStructureOfSorted (canonicalStructure (L := L) O hO P) R
    (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K := by
  letI := valuedStructureOfSorted (canonicalStructure (L := L) O hO P) R
  constructor
  · intro n f x
    change Structure.funMap f (homogeneousArgs (X := CanonicalSort O) (s := .vf)
      (expandHomogeneousArgs (X := CanonicalSort O) (s := .vf) x)) = Structure.funMap f x
    rw [homogeneousArgs_expand]
  · intro n r x
    change Structure.RelMap r (homogeneousArgs (X := CanonicalSort O) (s := .vf)
      (expandHomogeneousArgs (X := CanonicalSort O) (s := .vf) x)) = Structure.RelMap r x
    rw [homogeneousArgs_expand]

set_option linter.style.haveILetI false in
/-- The definable ring predicate retrieves the original valuation ring
on the canonical two-sorted expansion. -/
theorem recoveredRing_canonical (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1) :
    recoveredRing (canonicalStructure O hO P) minusOne = (O : Set K) := by
  let M := canonicalStructure (L := L) O hO P
  letI := valuedStructureOfSorted M (∅ : Set K)
  letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K :=
    valuedStructureOfSorted_expansion O hO P ∅
  have h : ((LHom.sumInl : L →ᴸ convexLanguage L).onTerm minusOne).realize
      (Empty.elim : Empty → K) = -1 := by
    rw [LHom.realize_onTerm, hm]
  ext x
  change x ∈ recoveredRing M minusOne ↔ x ∈ O
  unfold recoveredRing
  rw [h]
  change
    (letI := rvLinearOrder O hO
     (M.rvMap (-1) ≤ M.rvMap x ∧ M.rvMap x ≤ 1) ∨ unsignedValue O (M.rvMap x) = 1) ↔ x ∈ O
  rw [canonicalStructure_rvMap, canonicalStructure_rvMap]
  exact (mem_valuationRing_iff_signed_bounds O hO x).symm

theorem recoveredValuedStructure_canonical_eq (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1) :
    valuedStructureOfSorted (canonicalStructure O hO P)
        (recoveredRing (canonicalStructure O hO P) minusOne) = convexStructure O L := by
  rw [recoveredRing_canonical O hO P minusOne hm]
  let e : L →ᴸ convexLanguage L := LHom.sumInl
  let V := valuedStructureOfSorted (canonicalStructure (L := L) O hO P) (O : Set K)
  let C := convexStructure O L
  have hv : @LHom.IsExpansionOn L (convexLanguage L) e K _ V :=
    valuedStructureOfSorted_expansion O hO P O
  have hc : @LHom.IsExpansionOn L (convexLanguage L) e K _ C := convexStructure_expansion O
  apply Structure.ext
  · funext n f a
    cases f with
    | inl f => exact (hv.map_onFunction f a).trans (hc.map_onFunction f a).symm
    | inr f => exact f.elim
  · funext n r a
    cases r with
    | inl r => exact (hv.map_onRelation r a).trans (hc.map_onRelation r a).symm
    | inr r =>
      cases r
      exact propext (convexStructure_mem O a).symm

end Canonical

end GeneralizedEuler.Section2
