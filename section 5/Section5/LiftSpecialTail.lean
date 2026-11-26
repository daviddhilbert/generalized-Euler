module

public import Section5.SpecialChains

/-! A tail chain acts on the same coordinates when a first field
coordinate is adjoined and left fixed. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] {O : ValuationSubring K} {n : ℕ}
  {I J : Type}

def restrictRest {X : Type*} (i : Fin n)
    (a : {j : Fin (n+1) // j ≠ i.succ} → X) : {j : Fin n // j ≠ i} → X :=
  fun j => a ⟨j.val.succ, fun h => j.property (Fin.succ_inj.mp h)⟩

/-- The locus and focus are both read on the unchanged tail coordinates. -/
@[expose] def CoordinatePreparation.liftTail (C : CoordinatePreparation O (Fin n) I) :
    CoordinatePreparation O (Fin (n+1)) I where
  coord := C.coord.succ
  translation := {
    locus := {a | ((restrictRest C.coord a.1.1, a.1.2), a.2) ∈ C.translation.locus}
    focus := fun a => C.translation.focus (restrictRest C.coord a.1, a.2) }

theorem CoordinatePreparation.map_at_coordinate {F : Type*}
    (C : CoordinatePreparation O F I) (p : PreparationPoint O F I) :
    (C.map p).1 C.coord = p.1 C.coord -
      C.translation.offset (C.splitSource p).1 (rv O (p.1 C.coord)) := by
  classical
  simp [CoordinatePreparation.map, CoordinatePreparation.packTarget, CoordinatePreparation.splitSource,
    RelativeTranslation.map, splitCoordinate]

theorem CoordinatePreparation.liftTail_map (C : CoordinatePreparation O (Fin n) I)
    (p : PreparationPoint O (Fin (n+1)) I) :
    C.liftTail.map p = liftTailMap C.map p := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact C.liftTail.untouched p ((Fin.succ_ne_zero _).symm)
    · by_cases h : j = C.coord
      · subst j
        have hnew := C.liftTail.map_at_coordinate p
        have hold := C.map_at_coordinate (tailPoint p)
        change (C.liftTail.map p).1 C.liftTail.coord = (C.map (tailPoint p)).1 C.coord
        rw [hnew, hold]
        rfl
      · exact (C.liftTail.untouched p (fun eq => h (Fin.succ_inj.mp eq))).trans
          (C.untouched (tailPoint p) h).symm
  · funext i
    cases i <;> rfl

theorem tailPoint_label_eq (a b : PreparationPoint O (Fin (n+1)) I)
    (h : preparationLabel a = preparationLabel b) :
    preparationLabel (tailPoint a) = preparationLabel (tailPoint b) := by
  obtain ⟨hVF,hRV⟩ := Prod.mk.inj h
  refine Prod.ext ?_ hRV
  funext i
  exact congrFun hVF i.succ

theorem CoordinatePreparation.liftTail_valid
    (C : CoordinatePreparation O (Fin n) I) (A : Set (PreparationPoint O (Fin n) I))
    (hA : C.ValidOn O A) : C.liftTail.ValidOn O (tailPoint ⁻¹' A) := by
  intro p hp hl
  have htail : tailPoint p ∈ preparationHull O A := by
    obtain ⟨z,hz,he⟩ := hp
    exact ⟨tailPoint z,hz,tailPoint_label_eq z p he⟩
  exact hA (tailPoint p) htail hl

theorem image_liftTailMap
    (f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) J)
    (A : Set (PreparationPoint O (Fin n) I)) :
    liftTailMap f '' (tailPoint ⁻¹' A) = tailPoint ⁻¹' (f '' A) := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨tailPoint q,hq,rfl⟩
  · rintro ⟨q,hq,he⟩
    refine ⟨joinHead (q,p.1 0), hq, ?_⟩
    change joinHead (f q,p.1 0) = p
    rw [he]
    exact joinHead_separate p

/-- Replay a tail chain over an unchanged first field coordinate. -/
theorem SpecialChain.liftTail {A : Set (PreparationPoint O (Fin n) I)}
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) J}
    (h : SpecialChain O (Fin n) A f) :
    SpecialChain O (Fin (n+1)) (tailPoint ⁻¹' A) (liftTailMap f) := by
  induction h with
  | id A =>
    exact SpecialChain.congr (.id (tailPoint ⁻¹' A)) (fun p _ => (joinHead_separate p).symm)
  | translation A C hC =>
    exact SpecialChain.congr (.translation _ C.liftTail (C.liftTail_valid A hC)) (fun p _ => C.liftTail_map p)
  | regularization A source recover =>
    let projected := Sum.map Fin.succ _root_.id ∘ source
    have eq (p) : regularizeBy O projected p = liftTailMap (regularizeBy O source) p := by
      refine Prod.ext ?_ ?_
      · change p.1 = Fin.cons (p.1 0) (p.1 ∘ Fin.succ)
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      · funext i
        change Sum.elim (rv O ∘ p.1) p.2 (Sum.map Fin.succ _root_.id (source i)) =
          Sum.elim (rv O ∘ p.1 ∘ Fin.succ) p.2 (source i)
        cases source i <;> rfl
    have hrec a (ha : a ∈ tailPoint ⁻¹' A) b (hb : b ∈ tailPoint ⁻¹' A)
        (he : preparationLabel (regularizeBy O projected a) = preparationLabel (regularizeBy O projected b)) :
        a.2 = b.2 := by
      simp only [eq] at he
      have h := tailPoint_label_eq _ _ he
      exact recover _ ha _ hb h
    exact SpecialChain.congr (.regularization _ projected hrec) (fun p _ => eq p)
  | @append _ _ _ A f _ hf hg ihf ihg =>
    have guide := image_liftTailMap f A
    have lifted := SpecialChain.append ihf (guide.symm ▸ ihg)
    exact lifted.congr (fun p _ => rfl)
  | congr hf he ih =>
    apply ih.congr
    intro p hp
    exact congrArg (fun a => joinHead (a,p.1 0)) (he hp)

end GeneralizedEuler.Section5
