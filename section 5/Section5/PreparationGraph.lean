module

public import Section5.FixedBaseCenters

/-! Definability of unary preparations over their original two-sorted base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K)

/-- The initial leading term and one further leading term per step. -/
@[expose] def HistoryIndex : ℕ → Type
  | 0 => Unit
  | n + 1 => HistoryIndex n ⊕ Unit

def lastIndex : (n : ℕ) → HistoryIndex n
  | 0 => ()
  | _ + 1 => .inr ()

def decodeHistory : (n : ℕ) → (HistoryIndex n → RV0 O) → PreparationLabels O (RV0 O) n
  | 0, t => ⟨t ()⟩
  | n + 1, t => (decodeHistory n (t ∘ Sum.inl), t (.inr ()))

def encodeHistory : (n : ℕ) → PreparationLabels O (RV0 O) n → HistoryIndex n → RV0 O
  | 0, h => fun _ => h.down
  | n + 1, h => Sum.elim (encodeHistory n h.1) (fun _ => h.2)

theorem decode_encode_history (n : ℕ) (h : PreparationLabels O (RV0 O) n) :
    decodeHistory O n (encodeHistory O n h) = h := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih h.1) rfl

theorem encode_decode_history (n : ℕ) (t : HistoryIndex n → RV0 O) :
    encodeHistory O n (decodeHistory O n t) = t := by
  induction n with
  | zero => funext i; cases i; rfl
  | succ n ih =>
    funext i
    rcases i with i | ⟨⟩
    · exact congrFun (ih (t ∘ Sum.inl)) i
    · rfl

theorem lead_decode_history {C : Type*} (center : C → K) (cs : List C) (t : HistoryIndex cs.length → RV0 O) :
    ((UnaryPreparation.regularize (O := O)).prepare center cs).lead (decodeHistory O cs.length t) =
      t (lastIndex cs.length) := by
  cases cs <;> rfl

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K] {E : Type*}
  [L.Structure (Residue O)] (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)

local notation "M" => canonicalStructure (L := L) O hO power

variable (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (F : FieldTerms (convexLanguage L))

private abbrev GraphVars {X : TCsort → Type z} (B : ∀ s, Set (X s)) (n : ℕ) (s : TCsort) :=
  (B s : Type z) ⊕ MixedVariables 2 (HistoryIndex n) s

private def renameOld (n : ℕ) :
    ∀ s, GraphVars S.carrier n s → AddSortedVar (GraphVars S.carrier (n + 1)) .vf s
  | .vf => Sum.elim (fun c => .inl (.inl c))
      (Fin.cases (.inl (.inr 0)) (fun _ => .inr ⟨rfl⟩))
  | .rv => Sum.elim (fun c => .inl (.inl c)) (fun i => .inl (.inr (.inl i)))

private def graphFormula : (cs : List (S.carrier .vf)) →
    SortedFormula L E (GraphVars S.carrier cs.length)
  | [] =>
    let x : SortedTerm L E (GraphVars S.carrier 0) .vf := .var (.inr 0)
    let y : SortedTerm L E (GraphVars S.carrier 0) .vf := .var (.inr 1)
    (SortedFormula.equal y x).conjunction (.equal (rvOfVF y) (.var (.inr ())))
  | c :: cs =>
    let n := cs.length
    let x : SortedTerm L E (AddSortedVar (GraphVars S.carrier (n + 1)) .vf) .vf :=
      .var (.inl (.inr 0))
    let y : SortedTerm L E (AddSortedVar (GraphVars S.carrier (n + 1)) .vf) .vf :=
      .var (.inl (.inr 1))
    let old : SortedTerm L E (AddSortedVar (GraphVars S.carrier (n + 1)) .vf) .vf :=
      .var (.inr ⟨rfl⟩)
    let center : SortedTerm L E (AddSortedVar (GraphVars S.carrier (n + 1)) .vf) .vf :=
      .var (.inl (.inl c))
    let oldLead : SortedTerm L E (AddSortedVar (GraphVars S.carrier (n + 1)) .vf) .rv :=
      .var (.inl (.inr (.inl (lastIndex n))))
    let focus := (SortedFormula.equal oldLead rvZeroTerm).neg.conjunction
      (.equal (rvOfVF (subVF F center (subVF F x old))) oldLead)
    let move := (focus.conjunction (.equal y (subVF F x center))).disjunction
      (focus.neg.conjunction (.equal y old))
    let body := ((graphFormula cs).relabel (renameOld O hO power S n)).conjunction
      (move.conjunction (.equal (rvOfVF y) (.var (.inl (.inr (.inr ()))))))
    (SortedFormula.all .vf body.neg).neg

private def assignGraph {n : ℕ} (x y : K) (t : HistoryIndex n → RV0 O) :
    ∀ s, GraphVars S.carrier n s → CanonicalSort O s
  | .vf => Sum.elim Subtype.val (Fin.cases x (fun _ => y))
  | .rv => Sum.elim Subtype.val t

set_option linter.style.haveILetI false in
set_option maxHeartbeats 700000 in
private theorem eval_graphFormula
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (cs : List (S.carrier .vf)) (x y : K) (t : HistoryIndex cs.length → RV0 O) :
    (graphFormula O hO power S F cs).realize M (assignGraph O hO power S x y t) ↔
      ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).map x =
        (y, decodeHistory O cs.length t) := by
  classical
  induction cs generalizing y with
  | nil =>
    rw [graphFormula, SortedFormula.realize_conjunction]
    simp only [SortedFormula.realize, eval_rvOfVF O hO power, SortedTerm.realize]
    change y = x ∧ rv O y = t () ↔ (x - 0, ULift.up (rv O x)) =
      (y, ULift.up (t ()))
    constructor
    · rintro ⟨rfl, h⟩
      simp [h]
    · intro h
      obtain ⟨rfl, hv⟩ := Prod.mk.inj (by simpa only [sub_zero] using h)
      exact ⟨rfl, congrArg ULift.down hv⟩
  | cons c cs ih =>
    let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
    rw [graphFormula]
    simp only [SortedFormula.realize_neg, SortedFormula.realize_conjunction,
      SortedFormula.realize_disjunction, SortedFormula.realize, not_forall, not_not]
    have he (old : K) :
        (fun s => extendSortedAssignment (assignGraph O hO power S x y t) old s ∘ renameOld O hO power S cs.length s) =
          assignGraph O hO power S x old (t ∘ Sum.inl) := by
      funext s i
      cases s with
      | rv => cases i <;> rfl
      | vf =>
        rcases i with c | j
        · rfl
        · refine Fin.cases rfl (fun k => ?_) j
          fin_cases k
          rfl
    simp only [SortedFormula.realize_relabel, he, ih, eval_rvOfVF O hO power,
      eval_subVF O hO power F minusOne hm hF, realize_rvZeroTerm O hO power, SortedTerm.realize]
    let oldLabel := decodeHistory O (List.length cs) (t ∘ Sum.inl)
    let tag := (t ∘ Sum.inl) (lastIndex (List.length cs))
    change (∃ old : K, P.map x = (old, oldLabel) ∧
      (((tag ≠ 0 ∧ rv O (c.val - (x - old)) = tag) ∧ y = x - c.val) ∨
        (¬ (tag ≠ 0 ∧ rv O (c.val - (x - old)) = tag) ∧ y = old)) ∧
      rv O y = t (.inr ())) ↔
      (P.step c.val).map x = (y, (oldLabel, t (.inr ())))
    have ht : tag = P.lead oldLabel := (lead_decode_history O Subtype.val cs (t ∘ Sum.inl)).symm
    rw [ht]
    simp only [UnaryPreparation.map, UnaryPreparation.step, Prod.mk.injEq]
    constructor
    · rintro ⟨old, ⟨rfl, hlabel⟩, ⟨moved | fixed, hnew⟩⟩
      · rw [← hlabel] at moved
        rw [sub_sub_cancel] at moved
        have hoff : P.nextOffset c.val (P.label x) = c.val := by
          simp [UnaryPreparation.nextOffset, moved.1]
        rw [hoff]
        exact ⟨moved.2.symm, hlabel, moved.2 ▸ hnew⟩
      · rw [← hlabel] at fixed
        rw [sub_sub_cancel] at fixed
        have hoff : P.nextOffset c.val (P.label x) = P.offset (P.label x) := by
          simp [UnaryPreparation.nextOffset, fixed.1]
        rw [hoff]
        exact ⟨fixed.2.symm, hlabel, fixed.2 ▸ hnew⟩
    · rintro ⟨hy, hlabel, hnew⟩
      refine ⟨x - P.offset (P.label x), ⟨rfl, hlabel⟩, ?_, hy ▸ hnew⟩
      rw [← hlabel, sub_sub_cancel]
      by_cases hfocus : P.lead (P.label x) ≠ 0 ∧
          rv O (c.val - P.offset (P.label x)) = P.lead (P.label x)
      · exact Or.inl ⟨hfocus, by simpa [UnaryPreparation.nextOffset, hfocus] using hy.symm⟩
      · exact Or.inr ⟨hfocus, by simpa [UnaryPreparation.nextOffset, hfocus] using hy.symm⟩

set_option linter.style.haveILetI false in
/-- The graph of the actual finite sequence of centripetal transformations
is definable in the original two-sorted language, over the original base. -/
theorem preparationGraph_definable
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (cs : List (S.carrier .vf)) :
    SortedDefinableOver M S.carrier
      {v : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → CanonicalSort O s |
        ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).map (v .vf 0) =
          (v .vf 1, decodeHistory O cs.length (v .rv))} := by
  refine ⟨graphFormula O hO power S F cs, fun v => ?_⟩
  have he : assignGraph O hO power S (v .vf 0) (v .vf 1) (v .rv) =
      (fun s => Sum.elim Subtype.val (v s)) := by
    funext s i
    cases s with
    | rv => rfl
    | vf =>
      rcases i with c | j
      · rfl
      · refine Fin.cases rfl (fun k => ?_) j
        fin_cases k
        rfl
  rw [← he]
  exact (eval_graphFormula O hO power S F minusOne hm hF cs _ _ _).symm

end Canonical

end GeneralizedEuler.Section5
