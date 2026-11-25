module

public import Section3.AtomicShapes
import all Section3.AtomicShapes
public import Section3.ClosedDiscImages
public import Section3.BoundaryInduction

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

def IsPointOrOpen (S : Set K) : Prop :=
  (∃ x, S = {x}) ∨ ∃ c r, r ≠ 0 ∧ S = openDisc O c r

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem spread_lt_of_pointOrOpen [DenselyOrdered O.ValueGroup]
    {S : Set K} (h : IsPointOrOpen O S) {c : K} {r : O.ValueGroup} (hr : r ≠ 0)
    (hsub : S ⊆ closedDisc O c r) {x y : K} (hx : x ∈ S) (hy : y ∈ S) :
    O.valuation (x-y) < r := by
  rcases h with ⟨a,rfl⟩ | ⟨a,t,ht,rfl⟩
  · obtain rfl : x = a := hx
    have he : y = x := hy
    subst y
    simpa using pos_iff_ne_zero.mpr hr
  · have ha := mem_openDisc_center O ht a
    have hc := hsub ha
    rw [←closedDisc_change_center O hc] at hsub
    have hclosed := closedDisc_minimal_parent O ht hsub
    have htr := (closedDisc_subset_iff_radius O).mp hclosed
    rw [←openDisc_change_center O hy] at hx
    exact (show O.valuation (x-y) < t from hx).trans_le htr

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Any two points of the polydisc can be joined by changing one coordinate
at a time. A change of maximal open child in the image must therefore
already occur inside a single coordinate slice. -/
theorem image_lies_in_one_child [DenselyOrdered O.ValueGroup] {n : ℕ}
    (f : (Fin n → K) → K) (D : Fin n → Set K) {c : K} {r : O.ValueGroup} (hr : r ≠ 0)
    (rangeClosed : ∀ x, (∀ i, x i ∈ D i) → f x ∈ closedDisc O c r)
    (slices : ∀ i (a : Fin n → K), (∀ j, a j ∈ D j) →
      IsPointOrOpen O ((fun z => f (Function.update a i z)) '' D i))
    {x y : Fin n → K} (hx : ∀ i, x i ∈ D i) (hy : ∀ i, y i ∈ D i) :
    f y ∈ openDisc O (f x) r := by
  by_contra hfar
  let U := {a | f a ∈ openDisc O (f x) r}
  obtain ⟨i,z,w,hz,hw,hzx,hwx,hzw⟩ := exists_cut_coordinate U (mem_openDisc_center O hr (f x)) hfar
  have zIn j : z j ∈ D j := (hzx j).elim (fun h => h ▸ hx j) (fun h => h ▸ hy j)
  have wIn j : w j ∈ D j := (hwx j).elim (fun h => h ▸ hx j) (fun h => h ▸ hy j)
  have hwEq : Function.update z i (w i) = w := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · rw [Function.update_of_ne h]; exact hzw j h
  let S := (fun s => f (Function.update z i s)) '' D i
  have hsub : S ⊆ closedDisc O c r := by
    rintro _ ⟨s,hs,rfl⟩
    apply rangeClosed
    intro j
    by_cases h : j = i
    · subst j; simpa using hs
    · simpa [Function.update_of_ne h] using zIn j
  have hzs : f z ∈ S := ⟨z i,zIn i,by simp⟩
  have hws : f w ∈ S := ⟨w i,wIn i,congrArg f hwEq⟩
  have same : f w ∈ openDisc O (f z) r := spread_lt_of_pointOrOpen O (slices i z zIn) hr hsub hws hzs
  rw [openDisc_change_center O hz] at same
  exact hw same

include hO in
/-- Two points on either half of the annulus are a full diameter apart.
No distinguished center of either disc is used as a base parameter. -/
theorem annulus_has_diameter_pair (a : K) {r : O.ValueGroup} (hr : r ≠ 0) (upper : Bool) :
    let A := annulusSide upper (openDisc O a r) (closedDisc O a r)
    ∃ x ∈ A, ∃ y ∈ A, O.valuation (x-y) = r := by
  obtain ⟨d,hd⟩ := O.valuation_surjective r
  let u := |d|
  have hu : 0 < u := abs_pos.mpr ((map_ne_zero _).mp (hd.trans_ne hr))
  have hv : O.valuation u = r := (valuation_abs O d).trans hd
  have hsmall (z : K) (hz : z ∈ openDisc O a r) : |z-a| < u := by
    by_contra! h
    have h' := valuation_le_of_abs_le_abs O hO (by simpa [abs_of_pos hu] using h : |u| ≤ |z-a|)
    exact (hv ▸ h').not_gt hz
  have hh : O.valuation (u+u) ≤ r := (O.valuation.map_add u u).trans (by simp [hv])
  cases upper
  · refine ⟨a-u,⟨⟨a-u,?_,le_rfl⟩,?_⟩,a-(u+u),⟨⟨a-(u+u),?_,le_rfl⟩,?_⟩,?_⟩
    · change O.valuation (a-u-a) ≤ r; simp [sub_sub_cancel_left,hv]
    · intro z hz; linarith [(abs_lt.mp (hsmall z hz)).1]
    · change O.valuation (a-(u+u)-a) ≤ r; rwa [show a-(u+u)-a = -(u+u) by ring,O.valuation.map_neg]
    · intro z hz; linarith [(abs_lt.mp (hsmall z hz)).1]
    · rwa [show a-u-(a-(u+u))=u by ring]
  · refine ⟨a+(u+u),⟨?_,⟨a+(u+u),?_,le_rfl⟩⟩,a+u,⟨?_,⟨a+u,?_,le_rfl⟩⟩,?_⟩
    · intro z hz; linarith [(abs_lt.mp (hsmall z hz)).2]
    · change O.valuation (a+(u+u)-a) ≤ r; simpa using hh
    · intro z hz; linarith [(abs_lt.mp (hsmall z hz)).2]
    · change O.valuation (a+u-a) ≤ r; simp [hv]
    · rwa [show a+(u+u)-(a+u)=u by ring]

include hO in
/-- The higher-dimensional implication of 3.13. The four shapes for the
atomic image come from 3.11, and the one-coordinate slices use the unary
case over the base enlarged by the remaining coordinates. -/
theorem polydisc_image_of_unary_slices [DenselyOrdered O.ValueGroup] {n : ℕ}
    (f : (Fin n → K) → K) (D : Fin n → Set K)
    (slices : ∀ i (a : Fin n → K), (∀ j, a j ∈ D j) →
      IsPointOrOpen O ((fun z => f (Function.update a i z)) '' D i))
    (taxonomy : IsAtomicShape O (f '' {x | ∀ i, x i ∈ D i})) :
    IsPointOrOpen O (f '' {x | ∀ i, x i ∈ D i}) := by
  let A := f '' {x | ∀ i, x i ∈ D i}
  have exclude (c : K) (r : O.ValueGroup) (hr : r ≠ 0) (sub : A ⊆ closedDisc O c r)
      (pair : ∃ x ∈ A, ∃ y ∈ A, O.valuation (x-y) = r) : False := by
    obtain ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,he⟩ := pair
    have h := image_lies_in_one_child O f D hr (fun u hu => sub ⟨u,hu,rfl⟩) slices hy hx
    exact he.not_lt h
  rcases taxonomy with (point | ⟨c,r,hr,ho | hc⟩) | ⟨c,r,hr,side,hs⟩
  · exact Or.inl point
  · exact Or.inr ⟨c,r,hr,ho⟩
  · change A = _ at hc
    apply False.elim (exclude c r hr hc.subset ?_)
    obtain ⟨u,hu⟩ := O.valuation_surjective r
    rw [hc]
    exact ⟨c+u, by change O.valuation (c+u-c) ≤ r; simp [hu], c,
      mem_closedDisc_center O r c,by simpa using hu⟩
  · change A = _ at hs
    have conv := valuativeDisc_ordConnected O hO c (Iic r) (fun _ _ hxy hy => hxy.trans hy)
    have contained : A ⊆ closedDisc O c r := by
      rw [hs]
      cases side
      · rintro x ⟨⟨y,hy,hyx⟩,before⟩
        exact conv.out hy (mem_closedDisc_center O r c) ⟨hyx,(before c (mem_openDisc_center O hr c)).le⟩
      · rintro x ⟨after,⟨y,hy,hxy⟩⟩
        exact conv.out (mem_closedDisc_center O r c) hy ⟨(after c (mem_openDisc_center O hr c)).le,hxy⟩
    exact (exclude c r hr contained (hs.symm ▸ annulus_has_diameter_pair O hO c hr side)).elim

end GeneralizedEuler.Section3
