module

public import Section5.CenteredDiscContraction

/-! One simultaneous centripetal step in dimension one. The source
focus is the inverse image of the target focus. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

private theorem discToDisc_restrict_image {A B C : Set K} {f g : K → K}
    (dtdp : DiscToDiscOn O A B f g) (sub : C ⊆ A) :
    DiscToDiscOn O C (f '' C) f g := by
  obtain ⟨bij,inv,forward,backward⟩ := dtdp
  have im : f '' C ⊆ B := Set.image_subset_iff.2 (fun _ h => bij.mapsTo (sub h))
  exact ⟨⟨Set.mapsTo_image _ _,bij.injOn.mono sub,fun _ h => h⟩,
    ⟨fun _ h => inv.1 (sub h),fun _ h => inv.2 (im h)⟩,
    fun c r hr h => forward c r hr (h.trans sub),
    fun c r hr h => backward c r hr (h.trans im)⟩

/-- An individual target step records the RV label of the translated
point on the locus and the old leading term elsewhere. -/
def targetFocusLabel (L : Set (RV0 O)) (focus : RV0 O → K) (y : K) : RV0 O := by
  classical
  exact if rv O y ∈ L then rv O (y - focus (rv O y)) else rv O y

/-- In each target fiber at most one old source fiber is focused. -/
def sourceFocusLabel (L : Set (RV0 O)) (focus : RV0 O → K) (f g : K → K) (x : K) :
    RV0 O := by
  classical
  let t := rv O (f x)
  exact if t ∈ L ∧ rv O x = rv O (g (focus t)) then rv O (x - g (focus t)) else rv O x

/-- On an old source fiber the new source and target tests have
identical classes. The nonselected case uses the disc image avoiding
the focus, and the selected case uses centered disc-to-disc. -/
theorem paired_focus_matches_labels {A B : Set K} {f g : K → K}
    (dtdp : DiscToDiscOn O A B f g)
    (full : ∀ x ∈ A, ∀ y, rv O y = rv O x → y ∈ A)
    (contract : ∀ x ∈ A, ∀ y ∈ A, rv O x = rv O y → rv O (f x) = rv O (f y))
    (L : Set (RV0 O)) (focus : RV0 O → K)
    (focus_mem : ∀ t ∈ L, focus t ∈ B)
    {x y : K} (hx : x ∈ A) (hy : y ∈ A) (he : rv O x = rv O y) :
    sourceFocusLabel O L focus f g x = sourceFocusLabel O L focus f g y ↔
      targetFocusLabel O L focus (f x) = targetFocusLabel O L focus (f y) := by
  classical
  let t := rv O (f x)
  have ht : rv O (f y) = t := (contract x hx y hy he).symm
  by_cases zero : x = 0
  · have h0 : y = 0 := (rv_eq_zero_iff O).1 (he.symm.trans (zero ▸ map_zero (rv O)))
    simp [zero,h0]
  by_cases hl : t ∈ L
  · let c := g (focus t)
    have target : focus t ∈ B := focus_mem t hl
    obtain ⟨a,ha,hea⟩ := dtdp.1.surjOn target
    have fc : f c = focus t := dtdp.2.1.2 target
    let D := openDisc O x (O.valuation x)
    have rad : O.valuation x ≠ 0 := (map_ne_zero O.valuation).2 zero
    have xd : x ∈ D := mem_openDisc_center O rad x
    have yd : y ∈ D := by
      rw [show D = rv O ⁻¹' {rv O x} from (rv_fiber_eq_openDisc O zero).symm]
      exact he.symm
    have dSub : D ⊆ A := by
      intro z hz
      apply full x hx z
      exact (rv_eq_rv_iff_valuation O zero).2 hz
    obtain ⟨b,r,hr,dImage⟩ := dtdp.2.2.1 x (O.valuation x) rad dSub
    have fxd : f x ∈ openDisc O b r := dImage ▸ Set.mem_image_of_mem f xd
    have fyd : f y ∈ openDisc O b r := dImage ▸ Set.mem_image_of_mem f yd
    change (if rv O (f x) ∈ L ∧ rv O x = rv O (g (focus (rv O (f x))))
        then rv O (x-g (focus (rv O (f x)))) else rv O x) =
      (if rv O (f y) ∈ L ∧ rv O y = rv O (g (focus (rv O (f y))))
        then rv O (y-g (focus (rv O (f y)))) else rv O y) ↔
      (if rv O (f x) ∈ L then rv O (f x-focus (rv O (f x))) else rv O (f x)) =
      (if rv O (f y) ∈ L then rv O (f y-focus (rv O (f y))) else rv O (f y))
    rw [ht]
    change (if t ∈ L ∧ rv O x = rv O c then rv O (x-c) else rv O x) =
      (if t ∈ L ∧ rv O y = rv O c then rv O (y-c) else rv O y) ↔
      (if t ∈ L then rv O (f x-focus t) else t) =
      (if t ∈ L then rv O (f y-focus t) else t)
    by_cases hit : rv O x = rv O c
    · have hitY : rv O y = rv O c := he.symm.trans hit
      simp only [hl,hit,hitY,true_and,ite_true]
      have cd : c ∈ D := (rv_eq_rv_iff_valuation O zero).1 hit.symm
      have hdisc := discToDisc_restrict_image O dtdp dSub
      rw [dImage] at hdisc
      have hEq := centered_discToDisc_labels O hdisc cd xd yd
      simpa only [fc] using hEq
    · have hitY : rv O y ≠ rv O c := fun h => hit (he.trans h)
      simp only [hl,hit,hitY,true_and,ite_false,ite_true]
      have outside : focus t ∉ openDisc O b r := by
        intro hf
        obtain ⟨z,hz,hfz⟩ := show focus t ∈ f '' D from dImage.symm ▸ hf
        have hzc : z = c := by
          have hc : c ∈ A := by
            change g (focus t) ∈ A
            rw [← hea,dtdp.2.1.1 ha]
            exact ha
          exact dtdp.1.injOn (dSub hz) hc (hfz.trans fc.symm)
        exact hit ((rv_eq_rv_iff_valuation O zero).2 (hzc ▸ hz)).symm
      exact ⟨fun _ => rv_sub_const_of_openDisc_avoids O hr outside fxd fyd,fun _ => he⟩
  · unfold sourceFocusLabel targetFocusLabel
    rw [ht]
    have ht' : rv O (f x) = t := rfl
    simp only [ht',hl,false_and,ite_false,he]

end GeneralizedEuler.Section5
