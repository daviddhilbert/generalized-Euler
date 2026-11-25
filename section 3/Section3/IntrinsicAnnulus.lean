module

public import Section3.InducedResidueCharts
import all Section3.DiscRayQuotient
import all Section3.ChildSemilinear
import all Section3.AtomicShapes
import all Section2.ValuativeDisc

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem image_closedDisc (e : K ≃+* K) (ring : RespectsValuationRing O O e.toRingHom) (a b : K) (bn : b ≠ 0) :
    e '' closedDisc O a (O.valuation b) = closedDisc O (e a) (O.valuation (e b)) := by
  have test (v d z : K) (dn : d ≠ 0) : z ∈ closedDisc O v (O.valuation d) ↔ (z-v)/d ∈ O := by
    rw [←O.valuation_le_one_iff,map_div₀,div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr dn))]; rfl
  ext z
  obtain ⟨x,rfl⟩ := e.surjective z
  rw [e.injective.mem_set_image,test _ _ _ bn,test _ _ _ ((map_ne_zero _).mpr bn),←map_sub,←map_div₀]
  exact (ring _).symm

include hO in
/-- The closed parent of either half thin annulus is intrinsically
determined by the underlying set. Two points realize its diameter. -/
theorem annulus_parent_least (a b : K) {s : O.ValueGroup} (hs : s ≠ 0) (hb : O.valuation b = s)
    (bp : 0 < b) (upper : Bool) :
    let A := annulusSide upper (openDisc O a s) (closedDisc O a s)
    A ⊆ closedDisc O a s ∧ ∀ z r, A ⊆ closedDisc O z r → closedDisc O a s ⊆ closedDisc O z r := by
  let := residueLinearOrder O hO
  intro A
  have sub : A ⊆ closedDisc O a s := by
    intro x hx
    change x ∈ annulusSide upper (openDisc O a s) (closedDisc O a s) at hx
    rw [←childLocus_ray O hO a b hs hb bp upper] at hx
    exact hx.choose
  refine ⟨sub,fun z r inside => ?_⟩
  obtain ⟨x,hx,y,hy,dist⟩ := annulus_has_diameter_pair O hO a hs upper
  have big := closedDisc_change_center O (inside hy)
  have small := closedDisc_change_center O (sub hy)
  have le : s ≤ r := by rw [←dist]; exact (show x ∈ closedDisc O y r from big.symm ▸ inside hx)
  rw [←big,←small]; exact (closedDisc_subset_iff_radius O).mpr le

include hO in
theorem invariant_annulus_parent (a b : K) {s : O.ValueGroup} (hs : s ≠ 0) (hb : O.valuation b = s)
    (bp : 0 < b) (upper : Bool) (e : K ≃+* K) (ring : RespectsValuationRing O O e.toRingHom)
    (invariant : e '' annulusSide upper (openDisc O a s) (closedDisc O a s) =
      annulusSide upper (openDisc O a s) (closedDisc O a s)) :
    e '' closedDisc O a s = closedDisc O a s := by
  let A := annulusSide upper (openDisc O a s) (closedDisc O a s)
  let D := closedDisc O a s
  obtain ⟨sub,least⟩ := annulus_parent_least O hO a b hs hb bp upper
  have inc (f : K ≃+* K) (hf : RespectsValuationRing O O f.toRingHom) (pres : f '' A = A) : D ⊆ f '' D := by
    have toImage := image_mono (f := (f : K → K)) sub
    rw [pres] at toImage
    have eqn : f '' D = closedDisc O (f a) (O.valuation (f b)) := by
      simpa only [D,←hb] using image_closedDisc O f hf a b bp.ne'
    rw [eqn] at toImage ⊢; exact least _ _ toImage
  have pres : e '' A = A := invariant
  have inv : e.symm '' A = A := by
    calc e.symm '' A = e.symm '' (e '' A) := congrArg _ pres.symm
         _ = A := by rw [image_image]; simp only [e.symm_apply_apply,image_id']
  have invRing : RespectsValuationRing O O e.symm.toRingHom := fun y => by simpa using (ring (e.symm y)).symm
  have back := image_mono (f := (e : K → K)) (inc e.symm invRing inv)
  have idD : e '' (e.symm '' D) = D := by rw [image_image]; simp only [e.apply_symm_apply,image_id']
  rw [idD] at back
  exact back.antisymm (inc e ring invariant)

private theorem ray_origin {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (e : k ≃+* k) (ordered : StrictMono e) {α β : k} (upper : Bool)
    (ray : ∀ x : k, (if upper then 0 < α+β*e x else α+β*e x < 0) ↔ (if upper then 0 < x else x < 0)) : α = 0 := by
  have upperCase (a b : k) (h : ∀ x : k, (0 < a+b*x) ↔ 0 < x) : a = 0 := by
    have nonpos : a ≤ 0 := le_of_not_gt (fun pos => (lt_irrefl (0 : k)) ((h 0).mp (by simpa using pos)))
    apply le_antisymm nonpos
    by_contra! neg
    let x := -a / (2*(|b|+1))
    have den : 0 < 2*(|b|+1) := by positivity
    have xp : 0 < x := div_pos (neg_pos.mpr neg) den
    have small : b*x < -a := by
      have less : b < 2*(|b|+1) := by linarith [le_abs_self b,abs_nonneg b]
      have hlt := mul_lt_mul_of_pos_right less xp
      rwa [show 2*(|b|+1)*x = -a from mul_div_cancel₀ _ den.ne'] at hlt
    linarith [(h x).mpr xp]
  have pos (x : k) : 0 < e x ↔ 0 < x := by simpa using ordered.lt_iff_lt (a := 0) (b := x)
  have neg (x : k) : e x < 0 ↔ x < 0 := by simpa using ordered.lt_iff_lt (a := x) (b := 0)
  cases upper
  · apply neg_eq_zero.mp
    refine upperCase (-α) β (fun x => ?_)
    obtain ⟨y,hy⟩ := e.surjective (-x)
    have eqn := (ray y).trans (neg y).symm
    simp only [Bool.false_eq_true,ite_false,hy] at eqn
    constructor <;> intro h
    · have z := eqn.mp (by linarith); linarith
    · have z := eqn.mpr (by linarith); linarith
  · refine upperCase α β (fun x => ?_)
    obtain ⟨y,rfl⟩ := e.surjective x
    exact (ray y).trans (pos y).symm

include hO in
/-- The omitted child is fixed by every ordered valued-field
automorphism preserving the half. No center of the child is assumed
to be a parameter. -/
theorem invariant_annulus_child (a b : K) {s : O.ValueGroup} (hs : s ≠ 0) (hb : O.valuation b = s)
    (bp : 0 < b) (upper : Bool) (e : K ≃+* K) (ordered : StrictMono e)
    (ring : RespectsValuationRing O O e.toRingHom)
    (invariant : e '' annulusSide upper (openDisc O a s) (closedDisc O a s) =
      annulusSide upper (openDisc O a s) (closedDisc O a s)) : e a ∈ openDisc O a s := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let A := annulusSide upper (openDisc O a s) (closedDisc O a s)
  have fixed := invariant_annulus_parent O hO a b hs hb bp upper e ring invariant
  obtain ⟨α,β,_,_,act⟩ := semilinear_child_label O e ring a b hs hb fixed
  let σ := residueFieldEquiv O e ring
  have conv (x : closedDisc O a s) : x.val ∈ A ↔
      (if upper then 0 < childLabel O a b hs hb x else childLabel O a b hs hb x < 0) := by
    change x.val ∈ annulusSide upper (openDisc O a s) (closedDisc O a s) ↔ _
    rw [←childLocus_ray O hO a b hs hb bp upper]
    cases upper <;> exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨x.property,h⟩⟩
  have symm (y : Residue O) : (if upper then 0 < α+β*σ y else α+β*σ y < 0) ↔ (if upper then 0 < y else y < 0) := by
    obtain ⟨x,rfl⟩ := childLabel_surjective O a b hs hb y
    let ex : closedDisc O a s := ⟨e x.val,fixed.subset (mem_image_of_mem e x.property)⟩
    rw [show α+β*σ (childLabel O a b hs hb x) = childLabel O a b hs hb ex from (act x).symm,←conv,←conv]
    change e x.val ∈ A ↔ x.val ∈ A
    calc e x.val ∈ A ↔ e x.val ∈ e '' A := by rw [show e '' A = A from invariant]
         _ ↔ _ := e.injective.mem_set_image
  have zero := ray_origin σ (mapResidue_strictMono O O _ _ hO hO ordered) upper symm
  let cen : closedDisc O a s := ⟨a,mem_closedDisc_center O s a⟩
  have at0 := (discChildrenChart_eq_zero_iff O a b hs hb cen).mpr (mem_openDisc_center O hs a)
  have img := act cen
  change childLabel O a b hs hb cen = 0 at at0
  rw [at0,map_zero,mul_zero,add_zero,zero] at img
  exact (discChildrenChart_eq_zero_iff O a b hs hb _).mp img

end GeneralizedEuler.Section3
