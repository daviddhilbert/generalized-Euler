module

public import Section5.PairedMixedFocus
public import Section5.RelativeTranslation
import all Section5.PairedMixedFocus

/-! Realize the source focus selected by a target focus as a relative
centripetal transformation with the old label appended. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {R T : Type*} {A : Set (K × R)} {B : Set (K × T)}
  (e : A ≃ B) (C : Set (RV0 O × T)) (focus : RV0 O × T → B)

private def pairedSourceLocus : Set (R × RV0 O) :=
  {u | ∃ a : A,
    unaryMixedLabel O a.val = (u.2,u.1) ∧
    unaryMixedLabel O (e a).val ∈ C ∧
    unaryMixedLabel O (e.symm (focus (unaryMixedLabel O (e a).val))).val = (u.2,u.1)}

def pairedSourceTranslation : RelativeTranslation O (id : R → R) where
  locus := pairedSourceLocus O e C focus
  focus r t := by
    classical
    by_cases h : (r,t) ∈ pairedSourceLocus O e C focus
    · exact (e.symm (focus (unaryMixedLabel O (e h.choose).val))).val.1
    · exact 0

theorem pairedSourceTranslation_focus_lead {r : R} {t : RV0 O}
    (h : (r,t) ∈ (pairedSourceTranslation O e C focus).locus) :
    rv O ((pairedSourceTranslation O e C focus).focus r t) = t := by
  change (r,t) ∈ pairedSourceLocus O e C focus at h
  unfold pairedSourceTranslation
  dsimp only
  rw [dite_eq_left h]
  exact congrArg Prod.fst h.choose_spec.2.2

theorem pairedSourceTranslation_label
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e) (x : A) :
    rv O ((pairedSourceTranslation O e C focus).map (x.val.2,x.val.1)).2.1 =
      mixedSourceFocusLabel O e C focus x := by
  classical
  let r := x.val.2
  let t := rv O x.val.1
  let a := unaryMixedLabel O (e x).val
  let c := e.symm (focus a)
  have dom : (r,t) ∈ pairedSourceLocus O e C focus ↔
      a ∈ C ∧ unaryMixedLabel O x.val = unaryMixedLabel O c.val := by
    constructor
    · rintro ⟨w,hw,ht,he⟩
      have same : unaryMixedLabel O w.val = unaryMixedLabel O x.val := hw
      have va : unaryMixedLabel O (e w).val = a := contract w x same
      rw [va] at ht he
      exact ⟨ht,he.symm⟩
    · rintro ⟨ht,he⟩
      exact ⟨x,rfl,ht,he.symm⟩
  change rv O (x.val.1 - (pairedSourceTranslation O e C focus).offset r t) =
    (if a ∈ C ∧ unaryMixedLabel O x.val = unaryMixedLabel O c.val
      then rv O (x.val.1-c.val.1) else rv O x.val.1)
  by_cases h : (r,t) ∈ pairedSourceLocus O e C focus
  · rw [ite_eq_left (dom.1 h)]
    have same : unaryMixedLabel O h.choose.val = unaryMixedLabel O x.val := h.choose_spec.1
    have va : unaryMixedLabel O (e h.choose).val = a := contract h.choose x same
    unfold RelativeTranslation.offset pairedSourceTranslation
    dsimp only [id]
    rw [ite_eq_left h,dite_eq_left h,va]
  · rw [ite_eq_right (fun h' => h (dom.2 h'))]
    unfold RelativeTranslation.offset pairedSourceTranslation
    dsimp only [id]
    rw [ite_eq_right h,sub_zero]

def pairedTargetTranslation : RelativeTranslation O (id : T → T) where
  locus := {u | (u.2,u.1) ∈ C}
  focus tag t := (focus (t,tag)).val.1

theorem pairedTargetTranslation_label (y : B) :
    rv O ((pairedTargetTranslation O C focus).map (y.val.2,y.val.1)).2.1 =
      mixedTargetFocusLabel O C focus y := by
  classical
  unfold RelativeTranslation.map RelativeTranslation.offset pairedTargetTranslation mixedTargetFocusLabel
  change rv O (y.val.1 - (if unaryMixedLabel O y.val ∈ C
    then (focus (unaryMixedLabel O y.val)).val.1 else 0)) =
    (if unaryMixedLabel O y.val ∈ C then rv O (y.val.1 - (focus (unaryMixedLabel O y.val)).val.1)
      else rv O y.val.1)
  by_cases h : unaryMixedLabel O y.val ∈ C
  · rw [ite_eq_left h,ite_eq_left h]
  · rw [ite_eq_right h,ite_eq_right h,sub_zero]

end GeneralizedEuler.Section5
