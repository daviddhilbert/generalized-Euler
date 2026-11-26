module

public import Section3.DiscMaps

/-! Adding constants to the source and target coordinates does not
change the disc-to-disc property. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem add_mem_openDisc_iff {x c d : K} {r : O.ValueGroup} :
    x + d ∈ openDisc O (c+d) r ↔ x ∈ openDisc O c r := by
  change O.valuation ((x+d)-(c+d)) < r ↔ O.valuation (x-c) < r
  rw [add_sub_add_right_eq_sub]

theorem concentricOn_translated {A : Set K} {f : K → K} (h : ConcentricOn O A f) (a b : K) :
    ConcentricOn O {x | x + a ∈ A} (fun x => f (x+a)-b) := by
  intro c r hr hD
  have incl : openDisc O (c+a) r ⊆ A := by
    intro x hx
    have h := (add_mem_openDisc_iff O (x := x-a) (c := c) (d := a) (r := r)).1
      (by simpa only [sub_add_cancel] using hx)
    have hx' : (x-a)+a ∈ A := hD h
    simpa only [sub_add_cancel] using hx'
  obtain ⟨c',r',hr',himage⟩ := h (c+a) r hr incl
  refine ⟨c'-b,r',hr',?_⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    have h := (add_mem_openDisc_iff O (x := x) (c := c) (d := a) (r := r)).2 hx
    have fy : f (x+a) ∈ openDisc O c' r' := himage ▸ Set.mem_image_of_mem _ h
    apply (add_mem_openDisc_iff O (d := b)).1
    simpa only [sub_add_cancel] using fy
  · intro hy
    have h : y+b ∈ openDisc O c' r' := by
      simpa only [sub_add_cancel] using (add_mem_openDisc_iff O (d := b)).2 hy
    obtain ⟨x,hx,he⟩ := (show y+b ∈ f '' openDisc O (c+a) r from himage.symm ▸ h)
    have hh : (x-a)+a ∈ openDisc O (c+a) r := by simpa only [sub_add_cancel] using hx
    refine ⟨x-a,(add_mem_openDisc_iff O (d := a)).1 hh,?_⟩
    change f ((x-a)+a)-b = y
    rw [sub_add_cancel,he,add_sub_cancel_right]

theorem discToDisc_translated {A B : Set K} {f g : K → K} (h : DiscToDiscOn O A B f g) (a b : K) :
    DiscToDiscOn O {x | x + a ∈ A} {y | y + b ∈ B}
      (fun x => f (x+a)-b) (fun y => g (y+b)-a) := by
  obtain ⟨⟨maps,inj,surj⟩,⟨left,right⟩,forw,back⟩ := h
  refine ⟨⟨?_,?_,?_⟩,⟨?_,?_⟩,concentricOn_translated O forw a b,concentricOn_translated O back b a⟩
  · intro x hx
    change (f (x+a)-b)+b ∈ B
    rw [sub_add_cancel]
    exact maps hx
  · intro x hx y hy equal
    exact add_right_cancel (inj hx hy (sub_left_inj.1 equal))
  · intro y hy
    obtain ⟨x,hx,he⟩ := surj hy
    refine ⟨x-a,?_ ,?_⟩
    · change (x-a)+a ∈ A
      rwa [sub_add_cancel]
    · change f ((x-a)+a)-b = y
      rw [sub_add_cancel,he,add_sub_cancel_right]
  · intro x hx
    change g ((f (x+a)-b)+b)-a = x
    rw [sub_add_cancel,left hx,add_sub_cancel_right]
  · intro y hy
    change f ((g (y+b)-a)+a)-b = y
    rw [sub_add_cancel,right hy,add_sub_cancel_right]

end GeneralizedEuler.Section5
