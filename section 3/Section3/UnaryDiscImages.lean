module

public import Section3.PolydiscImages
public import Section3.CofinalValues
import all Section2.SignedValue
import all Section3.AtomicShapes
import all Section3.PolydiscImages

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO in
/-- A monotone map out of an open disc cannot cover a final segment of
the valuation ring if its inverse, extended off that segment, satisfies
3.2. Both directions of monotonicity are allowed. -/
theorem no_monotone_open_disc_onto_tail [DenselyOrdered O.ValueGroup]
    {a : K} {r : O.ValueGroup} (f : K → O) (g : O → K) (b : O)
    (htail : ∀ x > b, g x ∈ openDisc O a r ∧ f (g x) = x)
    (hmon : MonotoneOn f (openDisc O a r) ∨ AntitoneOn f (openDisc O a r))
    (stable : EventuallyConstantValue O hO (fun x => g x-a)) : False := by
  obtain ⟨b',hb'⟩ := stable
  let T := max b b'
  let y := T+1
  have hy : T < y := lt_add_one (T : K)
  have hyt := htail y ((le_max_left _ _).trans_lt hy)
  obtain ⟨s,hs,hsr⟩ := exists_between (show O.valuation (g y-a) < r from hyt.1)
  obtain ⟨d,hd⟩ := O.valuation_surjective s
  have absval : O.valuation |d| = s := (valuation_abs O d).trans hd
  have left : a-|d| ∈ openDisc O a r := by
    change O.valuation (a-|d|-a) < r
    rwa [sub_sub_cancel_left,O.valuation.map_neg,absval]
  have right : a+|d| ∈ openDisc O a r := by
    change O.valuation (a+|d|-a) < r
    rwa [add_sub_cancel_left,absval]
  let t := max T (max (f (a-|d|)) (f (a+|d|))) + 1
  have ht : max T (max (f (a-|d|)) (f (a+|d|))) < t := lt_add_one ((max T (max (f (a-|d|)) (f (a+|d|))) : O) : K)
  have hTt := (le_max_left _ _).trans_lt ht
  obtain ⟨hgt,hinv⟩ := htail t ((le_max_left _ _).trans_lt hTt)
  have he := ((signedValuation_eq_iff O hO _ _).mp
    (hb' t y ((le_max_right _ _).trans_lt hTt) ((le_max_right _ _).trans_lt hy))).2
  have hab : |g t-a| < |d| := by
    by_contra! h
    have hle := valuation_le_of_abs_le_abs O hO h
    rw [hd,he] at hle
    exact hs.not_ge hle
  have between := abs_lt.mp hab
  have bounds : f (g t) ≤ max (f (a-|d|)) (f (a+|d|)) := by
    rcases hmon with mh | ah
    · exact (mh hgt right (by linarith)).trans (le_max_right _ _)
    · exact (ah left hgt (by linarith)).trans (le_max_left _ _)
  rw [hinv] at bounds
  exact ((le_max_right _ _).trans_lt ht).not_ge bounds

/-- Parametrizing a finite-radius closed disc by O with a positive
direction gives the increasing affine coordinate in the unary argument. -/
theorem closed_disc_coordinate (c : K) {r : O.ValueGroup} (hr : r ≠ 0) :
    ∃ u : K, 0 < u ∧ O.valuation u = r ∧
      ∀ x : K, x ∈ closedDisc O c r ↔ (x-c)/u ∈ O := by
  obtain ⟨v,hv⟩ := O.valuation_surjective r
  let u := |v|
  have hu : 0 < u := abs_pos.mpr ((map_ne_zero _).mp (hv.trans_ne hr))
  have hval : O.valuation u = r := (valuation_abs O v).trans hv
  refine ⟨u,hu,hval,fun x => ?_⟩
  rw [←O.valuation_le_one_iff,map_div₀,hval,div_le_one₀ (pos_iff_ne_zero.mpr hr)]
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- If the image is an open disc avoiding zero, it is contained in one
ordinary RV fiber, as claimed in the last clause of 3.13. -/
theorem rv_constant_on_open_omitting_zero {a : K} {r : O.ValueGroup}
    (hr : r ≠ 0) (hzero : 0 ∉ openDisc O a r) {x : K} (hx : x ∈ openDisc O a r) :
    rv O x = rv O a := by
  have ha : a ≠ 0 := fun h => hzero (h ▸ mem_openDisc_center O hr a)
  have hle : r ≤ O.valuation a := by
    by_contra! h
    apply hzero
    change O.valuation (0-a) < r
    simpa using h
  exact (rv_eq_rv_iff_valuation O ha).mpr ((show O.valuation (x-a) < r from hx).trans_le hle)

include hO in
/-- The closed disc and either half of its thin annulus both contain the
whole image of (1,+∞) in O, with one of the two choices of direction. -/
theorem affine_tail_of_closed_or_half (c : K) {r : O.ValueGroup} (hr : r ≠ 0) {B : Set K}
    (shape : B = closedDisc O c r ∨
      ∃ side, B = annulusSide side (openDisc O c r) (closedDisc O c r)) :
    ∃ u : K, u ≠ 0 ∧ (∀ x ∈ B, (x-c)/u ∈ O) ∧
      ∀ z : O, 1 < z → c+u*z.val ∈ B := by
  obtain ⟨d,hd,hval,hcoord⟩ := closed_disc_coordinate O c hr
  have inside (z : O) : c+d*z.val ∈ closedDisc O c r := (hcoord _).mpr
    (by rw [add_sub_cancel_left,mul_div_cancel_left₀ _ hd.ne']; exact z.property)
  have small {x : K} (hx : x ∈ openDisc O c r) : |x-c| < d := by
    by_contra! h
    have hle := valuation_le_of_abs_le_abs O hO (show |d| ≤ |x-c| by rwa [abs_of_pos hd])
    exact (hval ▸ hle).not_gt hx
  rcases shape with rfl | ⟨side,rfl⟩
  · exact ⟨d,hd.ne',fun _ hx => (hcoord _).mp hx,fun z _ => inside z⟩
  have conv := valuativeDisc_ordConnected O hO c (Iic r) (fun _ _ hxy hy => hxy.trans hy)
  cases side
  · refine ⟨-d,neg_ne_zero.mpr hd.ne',?_,?_⟩
    · rintro x ⟨⟨y,hy,hyx⟩,before⟩
      rw [div_neg]
      exact O.neg_mem _ ((hcoord _).mp
        (conv.out hy (mem_closedDisc_center O r c) ⟨hyx,(before c (mem_openDisc_center O hr c)).le⟩))
    · intro z hz
      have hz' : (1 : K) < z.val := hz
      have hneg := inside (-z)
      refine ⟨⟨_,by simpa using hneg, le_rfl⟩,?_⟩
      intro y hy
      have := (abs_lt.mp (small hy)).1
      nlinarith [mul_lt_mul_of_pos_left hz' hd]
  · refine ⟨d,hd.ne',?_,?_⟩
    · rintro x ⟨after,⟨y,hy,hxy⟩⟩
      exact (hcoord _).mp (conv.out (mem_closedDisc_center O r c) hy
        ⟨(after c (mem_openDisc_center O hr c)).le,hxy⟩)
    · intro z hz
      refine ⟨?_,⟨_,inside z,le_rfl⟩⟩
      intro y hy
      have := (abs_lt.mp (small hy)).2
      have hz' : (1 : K) < z.val := hz
      nlinarith [mul_lt_mul_of_pos_left hz' hd]

include hO in
/-- Unary base of Lemma 3.13. The inverse is a total extension of the
inverse branch. Each affine substitution used in 3.2 may name its scale
and origin as ordinary parameters. -/
theorem unary_atomic_disc_image [DenselyOrdered O.ValueGroup] (a : K) (r : O.ValueGroup)
    (f g : K → K) (inverse : LeftInvOn g f (openDisc O a r))
    (mon : MonotoneOn f (openDisc O a r) ∨ AntitoneOn f (openDisc O a r))
    (shape : IsAtomicShape O (f '' openDisc O a r))
    (stable : ∀ c u : K, EventuallyConstantValue O hO (fun z => g (c+u*z.val)-a)) :
    IsPointOrOpen O (f '' openDisc O a r) := by
  classical
  let A := openDisc O a r
  let B := f '' A
  have exclude (c : K) (s : O.ValueGroup) (hs : s ≠ 0)
      (bad : B = closedDisc O c s ∨ ∃ side, B = annulusSide side (openDisc O c s) (closedDisc O c s)) :
      False := by
    obtain ⟨u,hu,coord,tail⟩ := affine_tail_of_closed_or_half O hO c hs bad
    let F (x : K) : O := if h : (f x-c)/u ∈ O then ⟨_,h⟩ else 0
    have valF {x : K} (hx : x ∈ A) : (F x : K) = (f x-c)/u := by
      simp [F, coord _ (mem_image_of_mem f hx)]
    let G (x : O) := g (c+u*x.val)
    have ht (x : O) (hx : 1 < x) : G x ∈ A ∧ F (G x) = x := by
      obtain ⟨w,hw,he⟩ := tail x hx
      have hgw : G x = w := (congrArg g he).symm.trans (inverse hw)
      rw [hgw]
      refine ⟨hw,Subtype.ext ?_⟩
      rw [valF hw,he,add_sub_cancel_left,mul_div_cancel_left₀ _ hu]
    by_cases pos : 0 < u
    · apply no_monotone_open_disc_onto_tail O hO F G 1 ht _ (stable c u)
      rcases mon with hm | hm
      · left; intro x hx y hy hxy
        change (F x : K) ≤ (F y : K)
        rw [valF hx,valF hy]; exact div_le_div_of_nonneg_right (sub_le_sub_right (hm hx hy hxy) _) pos.le
      · right; intro x hx y hy hxy
        change (F y : K) ≤ (F x : K)
        rw [valF hx,valF hy]; exact div_le_div_of_nonneg_right (sub_le_sub_right (hm hx hy hxy) _) pos.le
    · have neg := le_of_not_gt pos
      apply no_monotone_open_disc_onto_tail O hO F G 1 ht _ (stable c u)
      rcases mon with hm | hm
      · right; intro x hx y hy hxy
        change (F y : K) ≤ (F x : K)
        rw [valF hx,valF hy]; exact div_le_div_of_nonpos_of_le neg (sub_le_sub_right (hm hx hy hxy) _)
      · left; intro x hx y hy hxy
        change (F x : K) ≤ (F y : K)
        rw [valF hx,valF hy]; exact div_le_div_of_nonpos_of_le neg (sub_le_sub_right (hm hx hy hxy) _)
  rcases shape with (pt | ⟨c,s,hs,op | cl⟩) | ⟨c,s,hs,half⟩
  · exact Or.inl pt
  · exact Or.inr ⟨c,s,hs,op⟩
  · exact (exclude c s hs (Or.inl cl)).elim
  · exact (exclude c s hs (Or.inr half)).elim

end GeneralizedEuler.Section3
