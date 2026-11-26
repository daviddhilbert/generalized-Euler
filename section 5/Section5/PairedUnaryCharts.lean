module

public import Section5.PairedUnaryStep

/-! A paired step preserves the disc-to-disc charts needed to run
the next paired step. On each old chart both offsets are constant. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {R T : Type*} {A : Set (K × R)} {B : Set (K × T)}
  (e : A ≃ B) (C : Set (RV0 O × T)) (focus : RV0 O × T → B)

local notation "S" => pairedSourceTranslation O e C focus
local notation "T₁" => pairedTargetTranslation O C focus

/-- On a new source disc, recover the old disc from the retained
label and restrict the translated chart to the recovered subset. -/
theorem paired_unary_step_preserves_charts
    (full : IsUnaryPullback O A)
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) e)
    (charts : UnaryDiscCharts O e) :
    UnaryDiscCharts O (pairedUnaryConjugate O e C focus) := by
  let A' := recodeUnaryTranslation O S '' A
  let E := pairedUnaryConjugate O e C focus
  let s := unaryImageIso O A S
  have valid (r t) (h : (r,t) ∈ (S).locus) : rv O ((S).focus r t) = t :=
    pairedSourceTranslation_focus_lead O e C focus h
  have full' : IsUnaryPullback O A' := recodeUnaryTranslation_preserves_pullback O S A full valid
  intro x' nx
  obtain ⟨x,rfl⟩ := s.surjective x'
  have nz : x.val.1 ≠ 0 := fun h => nx (recodeUnaryTranslation_zero O S valid x.val h)
  obtain ⟨b,r,f,g,_,dtd,ag,oldCover⟩ := charts x nz
  let cs := (S).offset x.val.2 (rv O x.val.1)
  let ct := (T₁).offset (e x).val.2 (rv O (e x).val.1)
  let F (u : K) := f (u+cs)-ct
  let G (v : K) := g (v+ct)-cs
  let D := openDisc O (s x).val.1 (O.valuation (s x).val.1)
  let oldD := openDisc O x.val.1 (O.valuation x.val.1)
  let translated := {u | u+cs ∈ oldD}
  have translatedDtd := discToDisc_translated O dtd cs ct
  have sameOld {a : A}
      (h : unaryMixedLabel O (s a).val = unaryMixedLabel O (s x).val) :
      unaryMixedLabel O a.val = unaryMixedLabel O x.val :=
    congrArg (fun p : RV0 O × (R × RV0 O) => (p.2.2,p.2.1)) h
  have sameShift (a : A) (ha : unaryMixedLabel O a.val = unaryMixedLabel O x.val) :
      (s a).val.1 + cs = a.val.1 := by
    have e₁ := congrArg (fun p : RV0 O × R => p.1) ha
    have e₂ := congrArg (fun p : RV0 O × R => p.2) ha
    change rv O a.val.1 = rv O x.val.1 at e₁
    change a.val.2 = x.val.2 at e₂
    change a.val.1 - (S).offset a.val.2 (rv O a.val.1) + cs = a.val.1
    rw [e₁,e₂]
    exact sub_add_cancel _ _
  have fieldAg (a : A') (ha : unaryMixedLabel O a.val = unaryMixedLabel O (s x).val) :
      F a.val.1 = (E a).val.1 := by
    obtain ⟨u,rfl⟩ := s.surjective a
    have same := sameOld ha
    have next := contract u x same
    have e₁ := congrArg (fun p : RV0 O × T => p.1) next
    have e₂ := congrArg (fun p : RV0 O × T => p.2) next
    change rv O (e u).val.1 = rv O (e x).val.1 at e₁
    change (e u).val.2 = (e x).val.2 at e₂
    change f ((s u).val.1+cs)-ct = (pairedUnaryConjugate O e C focus (unaryImageIso O A S u)).val.1
    rw [sameShift u same,ag u same,pairedUnaryConjugate_apply O e C focus u]
    change (e u).val.1-ct = (e u).val.1 - (T₁).offset (e u).val.2 (rv O (e u).val.1)
    rw [e₁,e₂]
  have cover (z : K) (hz : z ∈ D) :
      ∃ a : A', a.val.1 = z ∧ unaryMixedLabel O a.val = unaryMixedLabel O (s x).val := by
    have lead := (rv_eq_rv_iff_valuation O nx).2 hz
    have he : unaryMixedLabel O (z,(s x).val.2) = unaryMixedLabel O (s x).val := Prod.ext lead rfl
    exact ⟨⟨(z,(s x).val.2),full' _ (s x).property _ he.symm⟩,rfl,he⟩
  have sub : D ⊆ translated := by
    intro z hz
    obtain ⟨a,ha,hLabel⟩ := cover z hz
    obtain ⟨u,rfl⟩ := s.surjective a
    have h := sameOld hLabel
    have core : u.val.1 ∈ oldD :=
      (rv_eq_rv_iff_valuation O nz).1 (congrArg (fun p : RV0 O × R => p.1) h)
    change z+cs ∈ oldD
    rw [← ha,sameShift u h]
    exact core
  have rne : O.valuation (s x).val.1 ≠ 0 := (map_ne_zero O.valuation).2 nx
  obtain ⟨b',r',hr',he⟩ := translatedDtd.2.2.1 _ _ rne sub
  have chart := discToDisc_restrict_image O translatedDtd sub
  change DiscToDiscOn O D (F '' D) F G at chart
  have he' : F '' D = openDisc O b' r' := he
  rw [he'] at chart
  exact ⟨b',r',F,G,hr',chart,fieldAg,cover⟩

end GeneralizedEuler.Section5
