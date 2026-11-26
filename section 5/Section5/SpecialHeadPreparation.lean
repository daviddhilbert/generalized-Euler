module

public import Section5.HeadRelativeStages
public import Section5.LiftSpecialTags

/-! The head preparation is a chain of genuine coordinate translations.
The program uses prepared tail labels for its loci and the unchanged
tail variables for its foci. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 UnaryPreparation

variable {K : Type*} [Field K] {O : ValuationSubring K} {n : ℕ}
  {I C : Type}

variable (centers : PreparationPoint O (Fin n) I → Option C → K)

@[expose] def headFamilyMap (cs : List C) (a : PreparationPoint O (Fin (n+1)) I) :
    PreparationPoint O (Fin (n+1)) (I ⊕ HistoryIndex cs.length) :=
  let t := tailPoint a
  let p := centerPreparation (O := O) (centers t) cs
  let y := p.map (a.1 0)
  (Fin.cons y.1 t.1, Sum.elim a.2 (encodeHistory O cs.length y.2))

def tailFromRest {X : Type*} (v : {j : Fin (n+1) // j ≠ 0} → X) : Fin n → X :=
  fun j => v ⟨j.succ, Fin.succ_ne_zero j⟩

@[expose] def headStage (cs : List C) (i : C) :
    CoordinatePreparation O (Fin (n+1)) (I ⊕ HistoryIndex cs.length) where
  coord := 0
  translation := {
    locus := {p | (((tailFromRest p.1.1, p.1.2 ∘ Sum.inl),
        decodeHistory O cs.length (p.1.2 ∘ Sum.inr)),p.2) ∈
      (headRelativeStage centers preparationLabel cs i).locus}
    focus := fun p t => (headRelativeStage centers preparationLabel cs i).focus
      ((tailFromRest p.1, p.2 ∘ Sum.inl), decodeHistory O cs.length (p.2 ∘ Sum.inr)) t }

variable (hzero : ∀ b, centers b none = 0)
  (stable : ∀ b b', preparationLabel b = preparationLabel b' →
    ∀ i j, rv O (centers b i - centers b j) = rv O (centers b' i - centers b' j))

include hzero stable in
theorem headStage_valid (cs : List C) (i : C) (A : Set (PreparationPoint O (Fin (n+1)) (I ⊕ HistoryIndex cs.length))) :
    (headStage centers cs i).ValidOn O A := by
  intro p _ h
  let b : PreparationPoint O (Fin n) I := (p.1 ∘ Fin.succ, p.2 ∘ Sum.inl)
  let history := decodeHistory O cs.length (p.2 ∘ Sum.inr)
  exact headRelativeStage_valid centers preparationLabel cs hzero stable i b history (rv O (p.1 0)) h

private def headStageTag (cs : List C) :
    I ⊕ HistoryIndex (cs.length+1) → Fin (n+1) ⊕ Option (I ⊕ HistoryIndex cs.length)
  | .inl j => .inr (some (.inl j))
  | .inr (.inl j) => .inr (some (.inr j))
  | .inr (.inr _) => .inl 0

private theorem old_head_leading_term (cs : List C) (i : C) (a : PreparationPoint O (Fin (n+1)) I) :
    ((headStage centers cs i).map (headFamilyMap centers cs a)).2 none =
      ((headStage centers cs i).map (headFamilyMap centers cs a)).2 (some (.inr (lastIndex cs.length))) := by
  let b := tailPoint a
  let P := centerPreparation (O := O) (centers b) cs
  rw [CoordinatePreparation.old_lead, CoordinatePreparation.old_aux]
  change rv O (P.map (a.1 0)).1 = encodeHistory O cs.length (P.label (a.1 0)) (lastIndex cs.length)
  have h := lead_decode_history O (centers b ∘ some) cs (encodeHistory O cs.length (P.label (a.1 0)))
  rw [decode_encode_history] at h
  exact (P.leading (a.1 0)).trans h

include hzero stable in
private theorem headStage_agrees (cs : List C) (i : C) (a : PreparationPoint O (Fin (n+1)) I) :
    regularizeBy O (headStageTag cs) ((headStage centers cs i).map (headFamilyMap centers cs a)) =
      headFamilyMap centers (i :: cs) a := by
  let b := tailPoint a
  let P := centerPreparation (O := O) (centers b) cs
  let C := headStage centers cs i
  let old := headFamilyMap centers cs a
  let y := (P.step (centers b (some i))).map (a.1 0)
  have hh : (C.map old).1 0 = y.1 := by
    have h := headRelativeStage_map centers preparationLabel cs hzero stable i b (a.1 0)
    have hx := C.map_at_coordinate old
    change (C.map old).1 C.coord = _
    rw [hx]
    have hdecode := decode_encode_history O cs.length (P.label (a.1 0))
    change (P.map (a.1 0)).1 -
      (headRelativeStage centers preparationLabel cs i).offset
        (b, decodeHistory O cs.length (encodeHistory O cs.length (P.label (a.1 0))))
        (rv O (P.map (a.1 0)).1) = _
    rw [hdecode]
    exact h
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.cases hh (fun j => ?_) j
    exact C.untouched old (Fin.succ_ne_zero j)
  · funext j
    rcases j with j | (j | t)
    · exact C.old_aux old (.inl j)
    · exact C.old_aux old (.inr j)
    · change rv O ((C.map old).1 0) = rv O y.1
      rw [hh]

include hzero stable in
/-- Each finite sequence of varying head centers gives a special chain
after the tail labels prepare the ordered center differences. -/
theorem specialHeadFamily (cs : List C) (A : Set (PreparationPoint O (Fin (n+1)) I)) :
    SpecialChain O (Fin (n+1)) A (headFamilyMap centers cs) := by
  induction cs with
  | nil =>
    let pick : I ⊕ HistoryIndex 0 → Fin (n+1) ⊕ I :=
      Sum.elim Sum.inr (fun _ => .inl 0)
    have recovers a (_ : a ∈ A) b (_ : b ∈ A)
        (he : preparationLabel (regularizeBy O pick a) = preparationLabel (regularizeBy O pick b)) :
        a.2 = b.2 := funext fun i => congrFun (congrArg Prod.snd he) (.inl i)
    refine SpecialChain.congr (.regularization A pick recovers) ?_
    intro a _
    refine Prod.ext ?_ ?_
    · funext j
      refine Fin.cases ?_ (fun _ => rfl) j
      simp [headFamilyMap, UnaryPreparation.map, UnaryPreparation.prepare, UnaryPreparation.regularize]
      rfl
    · funext j
      cases j with
      | inl _ => rfl
      | inr j => cases j; rfl
  | cons i cs ih =>
    let C := headStage centers cs i
    let D := C.map '' (headFamilyMap centers cs '' A)
    have recover a (ha : a ∈ D) b (hb : b ∈ D)
        (he : preparationLabel (regularizeBy O (headStageTag cs) a) =
          preparationLabel (regularizeBy O (headStageTag cs) b)) :
        a.2 = b.2 := by
      have haux := congrArg Prod.snd he
      have stay (j : I ⊕ HistoryIndex cs.length) : a.2 (some j) = b.2 (some j) := by
        cases j with
        | inl j => exact congrFun haux (.inl j)
        | inr j => exact congrFun haux (.inr (.inl j))
      have duplicate c (hc : c ∈ D) : c.2 none = c.2 (some (.inr (lastIndex cs.length))) := by
        obtain ⟨u,⟨v,_,rfl⟩,rfl⟩ := hc
        exact old_head_leading_term centers cs i v
      funext j
      cases j with
      | none => exact (duplicate a ha).trans ((stay _).trans (duplicate b hb).symm)
      | some j => exact stay j
    have moved : SpecialChain O (Fin (n+1)) (headFamilyMap centers cs '' A) C.map :=
      .translation _ C (headStage_valid centers hzero stable cs i _)
    exact SpecialChain.congr (.append ih (.append moved (.regularization D (headStageTag cs) recover)))
      (fun a _ => headStage_agrees centers hzero stable cs i a)

end GeneralizedEuler.Section5
