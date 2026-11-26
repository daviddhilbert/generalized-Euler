module

public import Section5.VerticalCenters

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

/-- The old and new head coordinates, the untouched tail, and the
entire leading-term history. -/
abbrev HistoryGraphVariables (d n : ℕ) : TCsort → Type
  | .vf => Fin 2 ⊕ Fin d
  | .rv => HistoryIndex n

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K] {E : Type*}
  [L.Structure (Residue O)] (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)

local notation "M" => canonicalStructure (L := L) O hO power

variable (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (F : FieldTerms (convexLanguage L))

variable {d : ℕ} {C : Type*}

private abbrev GraphVars {X : TCsort → Type z} (B : ∀ s, Set (X s)) (d n : ℕ) :=
  WithBase B (HistoryGraphVariables d n)

private def renameOld (n : ℕ) :
    ∀ s, GraphVars S.carrier d n s → AddSortedVar (GraphVars S.carrier d (n + 1)) .vf s
  | .vf => Sum.elim (fun c => .inl (.inl c))
      (Sum.elim (Fin.cases (.inl (.inr (.inl 0))) (fun _ => .inr ⟨rfl⟩))
        (fun j => .inl (.inr (.inr j))))
  | .rv => Sum.elim (fun c => .inl (.inl c)) (fun i => .inl (.inr (.inl i)))

private def renameCenter (n : ℕ) :
    ∀ s, WithBase S.carrier (MixedVariables d Empty) s →
      AddSortedVar (GraphVars S.carrier d (n + 1)) .vf s
  | .vf => fun i => .inl (Sum.map id Sum.inr i)
  | .rv => fun i => .inl (Sum.map id Empty.elim i)

private def graphFormula
    (terms : C → SortedTerm L E (WithBase S.carrier (MixedVariables d Empty)) .vf) :
    (cs : List C) → SortedFormula L E (GraphVars S.carrier d cs.length)
  | [] =>
    let x : SortedTerm L E (GraphVars S.carrier d 0) .vf := .var (.inr (.inl 0))
    let y : SortedTerm L E (GraphVars S.carrier d 0) .vf := .var (.inr (.inl 1))
    (SortedFormula.equal y x).conjunction (.equal (rvOfVF y) (.var (.inr ())))
  | c :: cs =>
    let n := cs.length
    let x : SortedTerm L E (AddSortedVar (GraphVars S.carrier d (n + 1)) .vf) .vf :=
      .var (.inl (.inr (.inl 0)))
    let y : SortedTerm L E (AddSortedVar (GraphVars S.carrier d (n + 1)) .vf) .vf :=
      .var (.inl (.inr (.inl 1)))
    let old : SortedTerm L E (AddSortedVar (GraphVars S.carrier d (n + 1)) .vf) .vf :=
      .var (.inr ⟨rfl⟩)
    let center := (terms c).relabel (renameCenter O hO power S n)
    let oldLead : SortedTerm L E (AddSortedVar (GraphVars S.carrier d (n + 1)) .vf) .rv :=
      .var (.inl (.inr (.inl (lastIndex n))))
    let focus := (SortedFormula.equal oldLead rvZeroTerm).neg.conjunction
      (.equal (rvOfVF (subVF F center (subVF F x old))) oldLead)
    let move := (focus.conjunction (.equal y (subVF F x center))).disjunction
      (focus.neg.conjunction (.equal y old))
    let body := ((graphFormula terms cs).relabel (renameOld O hO power S n)).conjunction
      (move.conjunction (.equal (rvOfVF y) (.var (.inl (.inr (.inr ()))))))
    (SortedFormula.all .vf body.neg).neg

private def assignGraph {n : ℕ} (x y : K) (tail : Fin d → K) (t : HistoryIndex n → RV0 O) :
    ∀ s, GraphVars S.carrier d n s → CanonicalSort O s
  | .vf => Sum.elim Subtype.val (Sum.elim (Fin.cases x (fun _ => y)) tail)
  | .rv => Sum.elim Subtype.val t

set_option linter.style.haveILetI false in
set_option maxHeartbeats 700000 in
private theorem eval_graphFormula
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (terms : C → SortedTerm L E (WithBase S.carrier (MixedVariables d Empty)) .vf)
    (cs : List C) (x y : K) (tail : Fin d → K) (t : HistoryIndex cs.length → RV0 O) :
    (graphFormula O hO power S F terms cs).realize M (assignGraph O hO power S x y tail t) ↔
      ((UnaryPreparation.regularize (O := O)).prepare
        (fun c => (terms c).realize M (centerAssignment O hO power S tail)) cs).map x =
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
    let val (j : C) := (terms j).realize M (centerAssignment O hO power S tail)
    let P := (UnaryPreparation.regularize (O := O)).prepare val cs
    rw [graphFormula]
    simp only [SortedFormula.realize_neg, SortedFormula.realize_conjunction,
      SortedFormula.realize_disjunction, SortedFormula.realize, not_forall, not_not]
    have he (old : K) :
        (fun s => extendSortedAssignment (assignGraph O hO power S x y tail t) old s ∘ renameOld O hO power S cs.length s) =
          assignGraph O hO power S x old tail (t ∘ Sum.inl) := by
      funext s i
      cases s with
      | rv => cases i <;> rfl
      | vf =>
        rcases i with c | (j | k)
        · rfl
        · refine Fin.cases rfl (fun k => ?_) j
          fin_cases k
          rfl
        · rfl
    have hcenter (old : K) :
        (fun s => extendSortedAssignment (assignGraph O hO power S x y tail t) old s ∘
          renameCenter O hO power S cs.length s) = centerAssignment O hO power S tail := by
      funext s i
      cases s with
      | vf => cases i <;> rfl
      | rv => rcases i with i | j; exacts [rfl, j.elim]
    simp only [SortedFormula.realize_relabel, he, ih, eval_rvOfVF O hO power,
      eval_subVF O hO power F minusOne hm hF, realize_rvZeroTerm O hO power,
      SortedTerm.realize_relabel, hcenter, SortedTerm.realize]
    let oldLabel := decodeHistory O (List.length cs) (t ∘ Sum.inl)
    let tag := (t ∘ Sum.inl) (lastIndex (List.length cs))
    change (∃ old : K, P.map x = (old, oldLabel) ∧
      (((tag ≠ 0 ∧ rv O ((val c) - (x - old)) = tag) ∧ y = x - (val c)) ∨
        (¬ (tag ≠ 0 ∧ rv O ((val c) - (x - old)) = tag) ∧ y = old)) ∧
      rv O y = t (.inr ())) ↔
      (P.step (val c)).map x = (y, (oldLabel, t (.inr ())))
    have ht : tag = P.lead oldLabel := (lead_decode_history O val cs (t ∘ Sum.inl)).symm
    rw [ht]
    simp only [UnaryPreparation.map, UnaryPreparation.step, Prod.mk.injEq]
    constructor
    · rintro ⟨old, ⟨rfl, hlabel⟩, ⟨moved | fixed, hnew⟩⟩
      · rw [← hlabel] at moved
        rw [sub_sub_cancel] at moved
        have hoff : P.nextOffset (val c) (P.label x) = (val c) := by
          simp [UnaryPreparation.nextOffset, moved.1]
        rw [hoff]
        exact ⟨moved.2.symm, hlabel, moved.2 ▸ hnew⟩
      · rw [← hlabel] at fixed
        rw [sub_sub_cancel] at fixed
        have hoff : P.nextOffset (val c) (P.label x) = P.offset (P.label x) := by
          simp [UnaryPreparation.nextOffset, fixed.1]
        rw [hoff]
        exact ⟨fixed.2.symm, hlabel, fixed.2 ▸ hnew⟩
    · rintro ⟨hy, hlabel, hnew⟩
      refine ⟨x - P.offset (P.label x), ⟨rfl, hlabel⟩, ?_, hy ▸ hnew⟩
      rw [← hlabel, sub_sub_cancel]
      by_cases hfocus : P.lead (P.label x) ≠ 0 ∧
          rv O ((val c) - P.offset (P.label x)) = P.lead (P.label x)
      · exact Or.inl ⟨hfocus, by simpa [UnaryPreparation.nextOffset, hfocus] using hy.symm⟩
      · exact Or.inr ⟨hfocus, by simpa [UnaryPreparation.nextOffset, hfocus] using hy.symm⟩

set_option linter.style.haveILetI false in
/-- The graph of a sequence with center terms depending on the untouched
field tuple is definable over the original base. -/
theorem preparationGraph_of_terms
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (terms : C → SortedTerm L E (WithBase S.carrier (MixedVariables d Empty)) .vf)
    (cs : List C) :
    SortedDefinableOver M S.carrier
      {v : ∀ s, HistoryGraphVariables d cs.length s → CanonicalSort O s |
        ((UnaryPreparation.regularize (O := O)).prepare (fun c =>
          (terms c).realize M (centerAssignment O hO power S (v .vf ∘ Sum.inr))) cs).map
          (v .vf (.inl 0)) = (v .vf (.inl 1), decodeHistory O cs.length (v .rv))} := by
  refine ⟨graphFormula O hO power S F terms cs, fun v => ?_⟩
  have he : assignGraph O hO power S (v .vf (.inl 0)) (v .vf (.inl 1))
      (v .vf ∘ Sum.inr) (v .rv) = (fun s => Sum.elim Subtype.val (v s)) := by
    funext s i
    cases s with
    | rv => rfl
    | vf =>
      rcases i with c | (j | k)
      · rfl
      · refine Fin.cases rfl (fun k => ?_) j
        fin_cases k
        rfl
      · rfl
  rw [← he]
  exact (eval_graphFormula O hO power S F minusOne hm hF terms cs _ _ _ _).symm

set_option linter.style.haveILetI false in
/-- Fixed centers from the base give the unary special bijection of
Lemma 5.4. -/
theorem preparationGraph_definable
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (cs : List (S.carrier .vf)) :
    SortedDefinableOver M S.carrier
      {v : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → CanonicalSort O s |
        ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).map (v .vf 0) =
          (v .vf 1, decodeHistory O cs.length (v .rv))} := by
  let terms (c : S.carrier .vf) :
      SortedTerm L E (WithBase S.carrier (MixedVariables 0 Empty)) .vf := .var (.inl c)
  let rename : ∀ s, HistoryGraphVariables 0 cs.length s → MixedVariables 2 (HistoryIndex cs.length) s
    | .vf => Sum.elim id Fin.elim0
    | .rv => id
  exact (preparationGraph_of_terms O hO power S F minusOne hm hF terms cs).pullback_relabel rename

end Canonical

end GeneralizedEuler.Section5
