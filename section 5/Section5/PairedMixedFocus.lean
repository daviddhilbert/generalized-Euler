module

public import Section5.PairedFocusStep

/-! One paired focus step with arbitrary old RV tags. If the inverse
focus has another source tag, the whole source disc is unselected. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {R T : Type*} {A : Set (K × R)} {B : Set (K × T)}

@[expose] def unaryMixedLabel {I : Type*} (x : K × I) : RV0 O × I := (rv O x.1,x.2)

def mixedTargetFocusLabel (C : Set (RV0 O × T)) (focus : RV0 O × T → B) (y : B) : RV0 O := by
  classical
  let t := unaryMixedLabel O y.val
  exact if t ∈ C then rv O (y.val.1 - (focus t).val.1) else t.1

def mixedSourceFocusLabel (f : A ≃ B) (C : Set (RV0 O × T))
    (focus : RV0 O × T → B) (x : A) : RV0 O := by
  classical
  let t := unaryMixedLabel O (f x).val
  let c := f.symm (focus t)
  exact if t ∈ C ∧ unaryMixedLabel O x.val = unaryMixedLabel O c.val
    then rv O (x.val.1 - c.val.1) else rv O x.val.1

/-- Match the new tests on a single old mixed label. The field maps
are those of the input disc with its tag fixed and of its image
with the target tag fixed. -/
theorem paired_mixed_focus_matches_labels (f : A ≃ B)
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) f)
    (C : Set (RV0 O × T)) (focus : RV0 O × T → B)
    (focusLabel : ∀ t ∈ C, unaryMixedLabel O (focus t).val = t)
    {x y : A} (same : unaryMixedLabel O x.val = unaryMixedLabel O y.val)
    (discCharts : x.val.1 ≠ 0 →
      ∃ (b : K) (r : O.ValueGroup) (f₀ g₀ : K → K),
        r ≠ 0 ∧ DiscToDiscOn O (openDisc O x.val.1 (O.valuation x.val.1)) (openDisc O b r) f₀ g₀ ∧
          (∀ a : A, unaryMixedLabel O a.val = unaryMixedLabel O x.val → f₀ a.val.1 = (f a).val.1) ∧
          (∀ u ∈ openDisc O x.val.1 (O.valuation x.val.1), ∃ a : A,
            a.val.1 = u ∧ unaryMixedLabel O a.val = unaryMixedLabel O x.val)) :
    mixedSourceFocusLabel O f C focus x = mixedSourceFocusLabel O f C focus y ↔
      mixedTargetFocusLabel O C focus (f x) = mixedTargetFocusLabel O C focus (f y) := by
  classical
  have oldFields : rv O x.val.1 = rv O y.val.1 := congrArg Prod.fst same
  by_cases xzero : x.val.1 = 0
  · have yzero : y.val.1 = 0 := (rv_eq_zero_iff O).1 (oldFields.symm.trans (xzero ▸ map_zero (rv O)))
    have oldTags : x.val.2 = y.val.2 := congrArg (fun z : RV0 O × R => z.2) same
    have xy : x = y := Subtype.ext (Prod.ext (xzero.trans yzero.symm) oldTags)
    subst y
    exact iff_of_true rfl rfl
  let t := unaryMixedLabel O (f x).val
  let c := f.symm (focus t)
  have tEq : unaryMixedLabel O (f y).val = t := (contract x y same).symm
  unfold mixedSourceFocusLabel mixedTargetFocusLabel
  rw [tEq]
  change (if t ∈ C ∧ unaryMixedLabel O x.val = unaryMixedLabel O c.val
      then rv O (x.val.1-c.val.1) else rv O x.val.1) =
    (if t ∈ C ∧ unaryMixedLabel O y.val = unaryMixedLabel O c.val
      then rv O (y.val.1-c.val.1) else rv O y.val.1) ↔
    (if t ∈ C then rv O ((f x).val.1-(focus t).val.1) else t.1) =
    (if t ∈ C then rv O ((f y).val.1-(focus t).val.1) else t.1)
  by_cases on : t ∈ C
  · obtain ⟨b,r,f₀,g₀,hr,dtd,agrees,cover⟩ := discCharts xzero
    have xDisc := mem_openDisc_center O ((map_ne_zero O.valuation).2 xzero) x.val.1
    have yDisc := (rv_eq_rv_iff_valuation O xzero).1 oldFields.symm
    have hx := agrees x rfl
    have hy := agrees y same.symm
    have fx := hx ▸ dtd.1.mapsTo xDisc
    have fy := hy ▸ dtd.1.mapsTo yDisc
    by_cases hit : unaryMixedLabel O x.val = unaryMixedLabel O c.val
    · have hitY := same.symm.trans hit
      have cDisc := (rv_eq_rv_iff_valuation O xzero).1 (congrArg Prod.fst hit).symm
      have cf := (agrees c hit.symm).trans (congrArg (fun y : B => y.val.1) (f.apply_symm_apply (focus t)))
      simpa only [on,hit,hitY,true_and,ite_true,hx,hy,cf] using
        (centered_discToDisc_labels O dtd cDisc xDisc yDisc)
    · have hitY : unaryMixedLabel O y.val ≠ unaryMixedLabel O c.val := fun h => hit (same.trans h)
      have avoids : (focus t).val.1 ∉ openDisc O b r := by
        intro has
        obtain ⟨v,hv,h⟩ := dtd.1.surjOn has
        obtain ⟨a,ha,hLabel⟩ := cover v hv
        have sameTag : (f a).val.2 = (f x).val.2 :=
          congrArg (fun z : RV0 O × T => z.2) (contract a x hLabel)
        have focusTag : (f x).val.2 = (focus t).val.2 :=
          (congrArg Prod.snd (focusLabel t on)).symm
        have whole : f a = focus t :=
          Subtype.ext (Prod.ext ((agrees a hLabel).symm.trans (ha ▸ h)) (sameTag.trans focusTag))
        exact hit (hLabel.symm.trans (congrArg (unaryMixedLabel O ∘ Subtype.val) (f.eq_symm_apply.2 whole)))
      simp only [on,hit,hitY,true_and,ite_true,ite_false]
      exact ⟨fun _ => rv_sub_const_of_openDisc_avoids O hr avoids fx fy,fun _ => oldFields⟩
  · simp only [on,false_and,ite_false]
    exact ⟨fun _ => trivial,fun _ => oldFields⟩

end GeneralizedEuler.Section5
