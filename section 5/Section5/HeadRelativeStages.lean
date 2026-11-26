module

public import Section5.HeadPreparation
public import Section5.RelativeTranslation

/-! Realize the individual steps in the varying head preparation as
relative centripetal transformations over the prepared tail labels. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 UnaryPreparation

variable {K : Type*} [Field K] {O : ValuationSubring K} {B Q I : Type*}
  (center : B → Option I → K) (tailLabel : B → Q) (cs : List I)

abbrev HeadHistory (O : ValuationSubring K) (cs : List I) :=
  PreparationLabels O (RV0 O) cs.length

/-- A head focus is calculated from the old field tail and history.
Its locus is indexed only by the prepared tail label and the RV history. -/
@[expose] def headRelativeStage (i : I) :
    RelativeTranslation O (fun p : B × HeadHistory O cs => (tailLabel p.1, p.2)) where
  locus := {p | ∃ b, tailLabel b = p.1.1 ∧
    (centerPreparation (O := O) (center b) cs).lead p.1.2 = p.2 ∧ p.2 ≠ 0 ∧
      rv O (center b (some i) - (centerPreparation (O := O) (center b) cs).offset p.1.2) = p.2}
  focus p _ := center p.1 (some i) - (centerPreparation (O := O) (center p.1) cs).offset p.2

variable
  (hzero : ∀ b, center b none = 0)
  (stable : ∀ b b', tailLabel b = tailLabel b' →
    ∀ i j, rv O (center b i - center b j) = rv O (center b' i - center b' j))

include hzero stable in
theorem headRelativeStage_locus (i : I) (b : B) (t : HeadHistory O cs) (s : RV0 O) :
    ((tailLabel b,t),s) ∈ (headRelativeStage center tailLabel cs i).locus ↔
      (centerPreparation (O := O) (center b) cs).lead t = s ∧ s ≠ 0 ∧
        rv O (center b (some i) - (centerPreparation (O := O) (center b) cs).offset t) = s := by
  constructor
  · rintro ⟨a,hab,hs,hn,he⟩
    have hlead := congrFun (centerPreparation_lead_independent (O := O) (center a) (center b) cs) t
    have h := (centerStep_same_locus (O := O) (center a) (center b)
      (hzero a) (hzero b) (stable a b hab) cs i t).1 ⟨hs.symm ▸ hn, he.trans hs.symm⟩
    exact ⟨hlead.symm.trans hs, hn, h.2.trans (hlead.symm.trans hs)⟩
  · rintro ⟨hs,hn,h⟩
    exact ⟨b,rfl,hs,hn,h⟩

include hzero stable in
theorem headRelativeStage_valid (i : I) (b : B) (t : HeadHistory O cs) (s : RV0 O)
    (hs : ((tailLabel b,t),s) ∈ (headRelativeStage center tailLabel cs i).locus) :
    s ≠ 0 ∧ rv O ((headRelativeStage center tailLabel cs i).focus (b,t) s) = s := by
  exact ((headRelativeStage_locus center tailLabel cs hzero stable i b t s).1 hs).2

include hzero stable in
/-- The first component of a step agrees with the old head map followed
by the corresponding relative centripetal translation. -/
theorem headRelativeStage_map (i : I) (b : B) (x : K) :
    let P := centerPreparation (O := O) (center b) cs
    let y := (P.map x).1
    ((headRelativeStage center tailLabel cs i).map ((b,P.label x),y)).2.1 =
      ((P.step (center b (some i))).map x).1 := by
  classical
  intro P y
  have hy : rv O y = P.lead (P.label x) := P.leading x
  let R := headRelativeStage (O := O) center tailLabel cs i
  have hloc :
      ((tailLabel b,P.label x),rv O y) ∈ R.locus ↔
        P.lead (P.label x) ≠ 0 ∧
          rv O (center b (some i) - P.offset (P.label x)) = P.lead (P.label x) := by
    rw [hy]
    exact (headRelativeStage_locus center tailLabel cs hzero stable i b _ _).trans
      ⟨fun h => h.2, fun h => ⟨rfl,h⟩⟩
  simp only [RelativeTranslation.map, UnaryPreparation.map, UnaryPreparation.step,
    RelativeTranslation.offset]
  change (x - P.offset (P.label x)) -
      (if ((tailLabel b,P.label x), rv O y) ∈ R.locus then
        center b (some i) - P.offset (P.label x) else 0) =
    x - P.nextOffset (center b (some i)) (P.label x)
  by_cases h : P.lead (P.label x) ≠ 0 ∧
      rv O (center b (some i) - P.offset (P.label x)) = P.lead (P.label x)
  · simp only [ite_eq_left (hloc.2 h), UnaryPreparation.nextOffset, ite_eq_left h,
      sub_sub_sub_cancel_right]
  · simp [hloc, h, UnaryPreparation.nextOffset]

end GeneralizedEuler.Section5
