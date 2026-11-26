module

public import Section3.DiscRayQuotient
public import Section3.ClosedDiscImages
import all Section3.DiscRayQuotient

/-! Translating corresponding focus points to zero makes an open
disc-to-disc bijection contract in both directions. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- On a disc avoiding a focus, the translated leading term is constant. -/
theorem rv_sub_const_of_openDisc_avoids {a c x y : K} {r : O.ValueGroup}
    (hr : r ≠ 0) (hc : c ∉ openDisc O a r)
    (hx : x ∈ openDisc O a r) (hy : y ∈ openDisc O a r) :
    rv O (x - c) = rv O (y - c) := by
  let D := openDiscCode O (a-c) r hr
  have zeroOut : 0 ∉ DiscCode.points O D := by
    change 0 ∉ DiscCode.points O (openDiscCode O (a-c) r hr)
    rw [openDiscCode_points]
    change ¬ O.valuation (0 - (a-c)) < r
    rw [zero_sub,neg_sub]
    exact hc
  obtain ⟨t,_,sub⟩ := D.exists_rv_fiber_of_zero_not_mem O zeroOut
  have shift (z : K) (hz : z ∈ openDisc O a r) : z-c ∈ DiscCode.points O D := by
    change z-c ∈ DiscCode.points O (openDiscCode O (a-c) r hr)
    rw [openDiscCode_points]
    change O.valuation ((z-c)-(a-c)) < r
    rwa [sub_sub_sub_cancel_right]
  exact (sub (shift x hx)).trans (sub (shift y hy)).symm

/-- On an open disc containing the focus, nonzero centered labels agree
exactly when there is a common open subdisc avoiding the focus. -/
theorem centered_rv_eq_iff_share_open {a c x y : K} {r : O.ValueGroup}
    (hc : c ∈ openDisc O a r) (hy : y ∈ openDisc O a r) (hne : y ≠ c) :
    rv O (x-c) = rv O (y-c) ↔ shareOpenSubdisc O (openDisc O a r \ {c}) x y := by
  let s := O.valuation (y-c)
  have hs : s ≠ 0 := (map_ne_zero O.valuation).2 (sub_ne_zero.2 hne)
  have small : s < r := by
    have h := hc
    rw [← openDisc_change_center O hy] at h
    change O.valuation (c-y) < r at h
    rw [← neg_sub y c,O.valuation.map_neg] at h
    exact h
  constructor
  · intro he
    have hx : x ∈ openDisc O y s := by
      have hh := (rv_eq_rv_iff_valuation O (sub_ne_zero.2 hne)).1 he
      rw [sub_sub_sub_cancel_right] at hh
      exact hh
    refine ⟨y,s,hs,?_,hx,mem_openDisc_center O hs y⟩
    intro z hz
    have zInside : z ∈ openDisc O a r := by
      rw [← openDisc_change_center O hy]
      exact (show O.valuation (z-y) < s from hz).trans small
    have zOut : z ≠ c := by
      intro he'
      have hh : c ∈ openDisc O y s := he' ▸ hz
      change O.valuation (c-y) < O.valuation (y-c) at hh
      rw [← neg_sub y c,O.valuation.map_neg] at hh
      exact (lt_irrefl _ hh)
    exact ⟨zInside,zOut⟩
  · rintro ⟨b,t,ht,sub,hx,hy'⟩
    exact rv_sub_const_of_openDisc_avoids O ht (fun h => (sub h).2 rfl) hx hy'

/-- A disc-to-disc bijection restricts to the domains with corresponding
points removed. -/
theorem discToDisc_punctured {A B : Set K} {f g : K → K}
    (dtdp : DiscToDiscOn O A B f g) {c : K} (hc : c ∈ A) :
    DiscToDiscOn O (A \ {c}) (B \ {f c}) f g := by
  obtain ⟨bij,inv,forw,back⟩ := dtdp
  have mt : Set.MapsTo f (A \ {c}) (B \ {f c}) := by
    intro x hx
    exact ⟨bij.mapsTo hx.1,fun h => hx.2 (bij.injOn hx.1 hc h)⟩
  have ms : Set.SurjOn f (A \ {c}) (B \ {f c}) := by
    intro y hy
    obtain ⟨x,hx,he⟩ := bij.surjOn hy.1
    exact ⟨x,⟨hx,fun h => hy.2 ((congrArg f h).symm.trans he).symm⟩,he⟩
  exact ⟨⟨mt,bij.injOn.mono Set.sdiff_subset,ms⟩,
    ⟨fun _ h => inv.1 h.1,fun _ h => inv.2 h.1⟩,
    fun c r hr sub => forw c r hr (sub.trans Set.sdiff_subset),
    fun c r hr sub => back c r hr (sub.trans Set.sdiff_subset)⟩

/-- The translated labels agree in the source exactly when they agree
in the target. This uses disc-to-disc in both directions. -/
theorem centered_discToDisc_labels {a b c x y : K} {r s : O.ValueGroup} {f g : K → K}
    (dtdp : DiscToDiscOn O (openDisc O a r) (openDisc O b s) f g)
    (hc : c ∈ openDisc O a r) (hx : x ∈ openDisc O a r) (hy : y ∈ openDisc O a r) :
    rv O (x-c) = rv O (y-c) ↔ rv O (f x - f c) = rv O (f y - f c) := by
  have bij := dtdp.1
  by_cases hn : y = c
  · subst y
    simp only [sub_self,map_zero,rv_eq_zero_iff,sub_eq_zero]
    exact ⟨congrArg f,bij.injOn hx hc⟩
  by_cases hnx : x = c
  · subst x
    rw [eq_comm, eq_comm (a := rv O (f c - f c))]
    simp only [sub_self,map_zero,rv_eq_zero_iff,sub_eq_zero]
    exact ⟨congrArg f,bij.injOn hy hc⟩
  have hn' : f y ≠ f c := fun he => hn (bij.injOn hy hc he)
  exact (centered_rv_eq_iff_share_open O hc hy hn).trans
    ((shareOpenSubdisc_image O (discToDisc_punctured O dtdp hc) ⟨hx,hnx⟩ ⟨hy,hn⟩).trans
      (centered_rv_eq_iff_share_open O (bij.mapsTo hc) (bij.mapsTo hy) hn').symm)

end GeneralizedEuler.Section5
