module

public import Section3.DiscMaps

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem closedDisc_subset_iff_radius {a : K} {r s : O.ValueGroup} :
    closedDisc O a r ⊆ closedDisc O a s ↔ r ≤ s := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := O.valuation_surjective r
    have he : O.valuation (d + a - a) = r := by rw [add_sub_cancel_right, hd]
    have h' : O.valuation (d + a - a) ≤ s := h (show d + a ∈ closedDisc O a r from he.le)
    rwa [he] at h'
  · intro h x hx
    change O.valuation (x - a) ≤ s
    exact le_trans hx h

theorem mem_open_iff_smaller_closed {a x : K} {r : O.ValueGroup} :
    x ∈ openDisc O a r ↔ ∃ c s, a ∈ closedDisc O c s ∧ x ∈ closedDisc O c s ∧
      closedDisc O c s ⊂ closedDisc O a r := by
  constructor
  · intro hx
    let s := O.valuation (x - a)
    refine ⟨a, s, mem_closedDisc_center O _ _, (le_refl s : O.valuation (x-a) ≤ s), ?_⟩
    exact ⟨(closedDisc_subset_iff_radius O).mpr (le_of_lt hx),
      fun h => (not_le_of_gt hx) ((closedDisc_subset_iff_radius O).mp h)⟩
  · rintro ⟨c,s,ha,hx,hsub⟩
    rw [← closedDisc_change_center O ha] at hx hsub
    have hs : s < r := lt_of_not_ge (fun h => hsub.2 ((closedDisc_subset_iff_radius O).mpr h))
    exact lt_of_le_of_lt hx hs

/-- Inside a closed parent in the domain, two-sided closed-disc preservation
carries the open child through a onto the open child through f(a).
This statement has no definability assumption. -/
theorem openChild_image {A B : Set K} {f g : K → K} (hf : MapsTo f A B)
    (hinv : InvOn g f A B) (forward : PreservesClosedDiscsOn O A f)
    (backward : PreservesClosedDiscsOn O B g)
    {a b : K} {r s : O.ValueGroup} (hP : closedDisc O a r ⊆ A)
    (himage : f '' closedDisc O a r = closedDisc O b s) :
    f '' openDisc O a r = openDisc O (f a) s := by
  have himg (D : Set K) (h : D ⊆ A) : g '' (f '' D) = D := by
    rw [image_image]
    exact (image_congr (fun x hx => hinv.1 (h hx))).trans (image_id D)
  have hba : f a ∈ closedDisc O b s := himage ▸ mem_image_of_mem f (mem_closedDisc_center O _ _)
  have htarget : f '' closedDisc O a r = closedDisc O (f a) s :=
    himage.trans (closedDisc_change_center O hba).symm
  have hT : closedDisc O (f a) s ⊆ B := htarget ▸ (mapsTo_iff_image_subset.mp (hf.mono_left hP))
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨c,t,ha,hx,hsm⟩ := (mem_open_iff_smaller_closed O).mp hx
    obtain ⟨d,u,hd⟩ := forward c t (hsm.1.trans hP)
    apply (mem_open_iff_smaller_closed O).mpr
    refine ⟨d,u,hd ▸ mem_image_of_mem f ha,hd ▸ mem_image_of_mem f hx, ?_⟩
    rw [← hd, ← htarget]
    refine ⟨image_mono hsm.1, fun hh => hsm.2 ?_⟩
    simpa only [himg _ hP, himg _ (hsm.1.trans hP)] using (image_mono hh (f := g))
  · intro hy
    obtain ⟨c,t,ha,hy,hsm⟩ := (mem_open_iff_smaller_closed O).mp hy
    obtain ⟨d,u,hd⟩ := backward c t (hsm.1.trans hT)
    have hback : g '' closedDisc O (f a) s = closedDisc O a r := htarget ▸ himg _ hP
    have hfa := hinv.1 (hP (mem_closedDisc_center O r a))
    have hgy : g y ∈ openDisc O a r := by
      apply (mem_open_iff_smaller_closed O).mpr
      refine ⟨d,u,hfa ▸ hd ▸ mem_image_of_mem g ha,hd ▸ mem_image_of_mem g hy,?_⟩
      rw [← hd, ← hback]
      refine ⟨image_mono hsm.1, fun hh => hsm.2 ?_⟩
      intro z hz
      obtain ⟨w,hw,he⟩ := hh (mem_image_of_mem g hz)
      have hinj := hinv.2.injOn (hT (hsm.1 hw)) (hT hz) he
      exact hinj ▸ hw
    exact ⟨g y, hgy, hinv.2 (hT (hsm.1 hy))⟩

/-- At a missing parent, a finite target radius with cofinal image radii
suffices. For a definable map the radius graph in the value group is piecewise
affine, which supplies a finite endpoint on the last affine piece. -/
theorem openDisc_image_of_radius_cut {a : K} {r s : O.ValueGroup}
    (f : K → K) (ρ : O.ValueGroup → O.ValueGroup)
    (himage : ∀ t < r, f '' closedDisc O a t = closedDisc O (f a) (ρ t))
    (hcut : ∀ v, v < s ↔ ∃ t < r, v ≤ ρ t) :
    f '' openDisc O a r = openDisc O (f a) s := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    let t := O.valuation (x - a)
    have hm : f x ∈ closedDisc O (f a) (ρ t) :=
      himage t hx ▸ mem_image_of_mem f (show O.valuation (x-a) ≤ t from le_refl t)
    exact (hcut _).mpr ⟨t,hx,hm⟩
  · intro hy
    obtain ⟨t,ht,hle⟩ := (hcut _).mp hy
    have hm : y ∈ f '' closedDisc O a t := (himage t ht).symm ▸ hle
    obtain ⟨x,hx,rfl⟩ := hm
    exact ⟨x,lt_of_le_of_lt hx ht,rfl⟩

/-- A positive affine germ in value coordinates has a finite endpoint.
The order isomorphism is the affine branch on the entire value group,
extended at zero in multiplicative notation. -/
theorem radius_cut_of_affine_germ {G : Type*} [LinearOrder G] [DenselyOrdered G]
    (ρ : G → G) {l r : G} (hl : l < r) (hmono : MonotoneOn ρ (Iio r))
    (e : G ≃o G) (hgerm : ∀ t ∈ Ioo l r, ρ t = e t) :
    ∀ v, v < e r ↔ ∃ t < r, v ≤ ρ t := by
  intro v
  constructor
  · intro hv
    have he : e.symm v < r := (e.lt_iff_lt.mp (by simpa using hv))
    obtain ⟨t,ht,htr⟩ := exists_between (max_lt hl he)
    have hlt := (le_max_left l (e.symm v)).trans_lt ht
    have het := (le_max_right l (e.symm v)).trans_lt ht
    refine ⟨t,htr,?_⟩
    rw [hgerm t ⟨hlt,htr⟩]
    simpa using (e.strictMono het).le
  · rintro ⟨t,htr,hv⟩
    obtain ⟨u,hu,hur⟩ := exists_between (max_lt hl htr)
    have hlu := (le_max_left l t).trans_lt hu
    have htu := (le_max_right l t).trans_lt hu
    exact (hv.trans (hmono htr hur htu.le)).trans_lt
      ((hgerm u ⟨hlu,hur⟩).trans_lt (e.strictMono hur))

/-- The radii of the images of nested closed discs are strictly increasing
when the map is injective. Consequently a terminal affine branch in the
value group can have neither zero nor negative slope. -/
theorem image_radii_strictMono {a : K} {r : O.ValueGroup} {f : K → K}
    (hi : InjOn f (openDisc O a r)) (ρ : O.ValueGroup → O.ValueGroup)
    (hm : ∀ t < r, f '' closedDisc O a t = closedDisc O (f a) (ρ t)) :
    StrictMonoOn ρ (Iio r) := by
  intro t ht u hu htu
  have htu' := (closedDisc_subset_iff_radius (a := a) O).mpr htu.le
  have hs := image_mono (f := f) htu'
  rw [hm _ ht, hm _ hu] at hs
  apply lt_of_le_of_ne ((closedDisc_subset_iff_radius O).mp hs)
  intro he
  apply htu.not_ge
  apply (closedDisc_subset_iff_radius (a := a) O).mp
  intro x hx
  have hfx : f x ∈ f '' closedDisc O a t := by
    rw [hm _ ht, he, ← hm _ hu]
    exact mem_image_of_mem f hx
  obtain ⟨y,hy,hyx⟩ := hfx
  have hy' : y ∈ openDisc O a r := (show O.valuation (y - a) ≤ t from hy).trans_lt ht
  have hx' : x ∈ openDisc O a r := (show O.valuation (x - a) ≤ u from hx).trans_lt hu
  exact hi hy' hx' hyx ▸ hy

/-- Forward implication for a definable map using the last affine branch of its
radius function (the value-group input from Theorem B). Apply to f and its
inverse for the corrected converse after 3.23. -/
theorem openDisc_image_of_affine_radius_germ [DenselyOrdered O.ValueGroup]
    {a : K} {r l : O.ValueGroup} (hl : l < r) {f : K → K}
    (hi : InjOn f (openDisc O a r)) (ρ : O.ValueGroup → O.ValueGroup)
    (hm : ∀ t < r, f '' closedDisc O a t = closedDisc O (f a) (ρ t))
    (e : O.ValueGroup ≃o O.ValueGroup) (hg : ∀ t ∈ Ioo l r, ρ t = e t) :
    f '' openDisc O a r = openDisc O (f a) (e r) :=
  openDisc_image_of_radius_cut O f ρ hm (radius_cut_of_affine_germ ρ hl
    (image_radii_strictMono O hi ρ hm).monotoneOn e hg)

/-- The one-variable instance of the cited piecewise-affine theorem used
here. Its input graph says exactly that the closed disc of radius t about
a has image the closed disc of radius ρ(t) about f(a). -/
def HasTerminalAffineRadius (A : Set K) (f : K → K) : Prop :=
  ∀ a r, r ≠ 0 → openDisc O a r ⊆ A → ∀ ρ : O.ValueGroup → O.ValueGroup,
    (∀ t < r, f '' closedDisc O a t = closedDisc O (f a) (ρ t)) →
    StrictMonoOn ρ (Iio r) →
    ∃ l < r, ∃ e : O.ValueGroup ≃o O.ValueGroup, ∀ t ∈ Ioo l r, ρ t = e t

theorem concentric_of_preservesClosed [DenselyOrdered O.ValueGroup] {A : Set K} {f : K → K}
    (hi : InjOn f A) (hclosed : PreservesClosedDiscsOn O A f)
    (hdef : HasTerminalAffineRadius O A f) : ConcentricOn O A f := by
  classical
  intro a r hr hsub
  have hex (t : O.ValueGroup) (ht : t < r) :
      ∃ s, f '' closedDisc O a t = closedDisc O (f a) s := by
    obtain ⟨b,s,he⟩ := hclosed a t (fun x hx => hsub
      (show O.valuation (x - a) < r from (show O.valuation (x - a) ≤ t from hx).trans_lt ht))
    have hm : f a ∈ closedDisc O b s := he ▸ mem_image_of_mem f (mem_closedDisc_center O t a)
    exact ⟨s, he.trans (closedDisc_change_center O hm).symm⟩
  let ρ (t : O.ValueGroup) := if h : t < r then (hex t h).choose else 0
  have hm (t : O.ValueGroup) (ht : t < r) :
      f '' closedDisc O a t = closedDisc O (f a) (ρ t) := by
    simpa [ρ,ht] using (hex t ht).choose_spec
  obtain ⟨l,hl,e,hg⟩ := hdef a r hr hsub ρ hm (image_radii_strictMono O (hi.mono hsub) ρ hm)
  refine ⟨f a,e r,?_,openDisc_image_of_affine_radius_germ O hl (hi.mono hsub) ρ hm e hg⟩
  have he : e 0 = 0 := e.map_bot
  exact (he ▸ e.injective.ne hr)

theorem discToDisc_of_preservesClosed_both_directions [DenselyOrdered O.ValueGroup]
    {A B : Set K} {f g : K → K} (hbij : BijOn f A B) (hinv : InvOn g f A B)
    (hf : PreservesClosedDiscsOn O A f) (hg : PreservesClosedDiscsOn O B g)
    (hdef : HasTerminalAffineRadius O A f) (hdefInv : HasTerminalAffineRadius O B g) :
    DiscToDiscOn O A B f g :=
  ⟨hbij, hinv, concentric_of_preservesClosed O hbij.injOn hf hdef,
    concentric_of_preservesClosed O hinv.2.injOn hg hdefInv⟩

end GeneralizedEuler.Section3
