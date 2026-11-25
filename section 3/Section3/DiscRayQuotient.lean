module

public import Section3.DiscGraphImages
public import Section2.ValuativeDisc
import all Section3.PolydiscImages
import all Section3.AtomicShapes

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

noncomputable abbrev childLabel (c d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (x : closedDisc O c r) : Residue O := discChildrenChart O c d hr hd ⟦x⟧

theorem childLabel_surjective (c d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r) :
    Function.Surjective (childLabel O c d hr hd) := by
  intro y
  obtain ⟨q,hq⟩ := (discChildrenChart O c d hr hd).surjective y
  induction q using Quotient.inductionOn with
  | h x => exact ⟨x,hq⟩

theorem childLabel_equal_iff (c d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (x y : closedDisc O c r) : childLabel O c d hr hd x = childLabel O c d hr hd y ↔
      (x : K) ∈ openDisc O (y : K) r :=
  (discChildrenChart O c d hr hd).injective.eq_iff.trans (openChildSetoid_fiber O c hr x y)

def childLocus (c d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (W : Set (Residue O)) : Set K := {x | ∃ h : x ∈ closedDisc O c r, childLabel O c d hr hd ⟨x,h⟩ ∈ W}

theorem childLocus_univ (c d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r) :
    childLocus O c d hr hd univ = closedDisc O c r := by
  ext x; exact ⟨fun ⟨h,_⟩ => h,fun h => ⟨h,trivial⟩⟩

/-- Sharing a maximal child can be detected inside any union of children,
without naming its parent in the test. -/
def shareOpenSubdisc (A : Set K) (x y : K) : Prop :=
  ∃ b t, t ≠ 0 ∧ openDisc O b t ⊆ A ∧ x ∈ openDisc O b t ∧ y ∈ openDisc O b t

theorem same_child_iff_share_open [DenselyOrdered O.ValueGroup] (c d : K) {r : O.ValueGroup}
    (hr : r ≠ 0) (hd : O.valuation d = r) (W : Set (Residue O)) (x y : closedDisc O c r)
    (hy : childLabel O c d hr hd y ∈ W) :
    childLabel O c d hr hd x = childLabel O c d hr hd y ↔
      shareOpenSubdisc O (childLocus O c d hr hd W) x y := by
  rw [childLabel_equal_iff]
  constructor
  · intro hx
    refine ⟨y,r,hr,?_,hx,mem_openDisc_center O hr _⟩
    intro z hz
    have hm := (openChild_maximal_proper O hr y.property).2.1 hz
    exact ⟨hm,((childLabel_equal_iff O c d hr hd ⟨z,hm⟩ y).mpr hz).symm ▸ hy⟩
  · rintro ⟨b,t,ht,sub,hx,hy'⟩
    have contain : openDisc O b t ⊆ closedDisc O c r := fun z hz => (sub hz).choose
    have hb := contain (mem_openDisc_center O ht b)
    rw [←closedDisc_change_center O hb] at contain
    have tr := (closedDisc_subset_iff_radius O).mp (closedDisc_minimal_parent O ht contain)
    rw [←openDisc_change_center O hy'] at hx
    exact (show O.valuation ((x : K)-y) < t from hx).trans_le tr

theorem shareOpenSubdisc_image {A B : Set K} {f g : K → K} (map : DiscToDiscOn O A B f g)
    {x y : K} (hx : x ∈ A) (hy : y ∈ A) :
    shareOpenSubdisc O A x y ↔ shareOpenSubdisc O B (f x) (f y) := by
  obtain ⟨bij,inv,forward,back⟩ := map
  constructor
  · rintro ⟨a,r,hr,hA,hx,hy⟩
    obtain ⟨b,s,hs,he⟩ := forward a r hr hA
    exact ⟨b,s,hs,he ▸ (image_subset_iff.mpr (fun _ h => bij.mapsTo (hA h))),
      he ▸ mem_image_of_mem f hx,he ▸ mem_image_of_mem f hy⟩
  · rintro ⟨b,s,hs,hB,hfx,hfy⟩
    obtain ⟨a,r,hr,he⟩ := back b s hs hB
    have ga : MapsTo g B A := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := bij.surjOn hz
      simpa [inv.1 hw] using hw
    exact ⟨a,r,hr,he ▸ (image_subset_iff.mpr (fun _ h => ga (hB h))),
      inv.1 hx ▸ he ▸ mem_image_of_mem g hfx,inv.1 hy ▸ he ▸ mem_image_of_mem g hfy⟩

/-- A bijection respecting the child equivalences induces an actual
equivalence on their labels. The displayed identity holds for every lift. -/
private theorem quotient_equiv {A B R S : Type*} (p : A → R) (q : B → S) (f : A ≃ B)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (same : ∀ x y, p x = p y ↔ q (f x) = q (f y)) :
    ∃ h : R ≃ S, ∀ x, h (p x) = q (f x) := by
  let h (u : R) := q (f (hp u).choose)
  have eqn (x : A) : h (p x) = q (f x) := (same _ _).mp (hp _).choose_spec
  have bij : Function.Bijective h := by
    constructor
    · intro x y he
      obtain ⟨a,rfl⟩ := hp x
      obtain ⟨b,rfl⟩ := hp y
      exact (same _ _).mpr ((eqn a).symm.trans (he.trans (eqn b)))
    · intro z
      obtain ⟨b,rfl⟩ := hq z
      exact ⟨p (f.symm b),by rw [eqn,f.apply_symm_apply]⟩
  exact ⟨Equiv.ofBijective h bij,eqn⟩

noncomputable def labelOnLocus (c d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (W : Set (Residue O)) (x : childLocus O c d hr hd W) : W :=
  ⟨childLabel O c d hr hd ⟨x.val,x.property.choose⟩,x.property.choose_spec⟩

theorem labelOnLocus_surjective (c d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (W : Set (Residue O)) : Function.Surjective (labelOnLocus O c d hr hd W) := by
  intro y
  obtain ⟨x,hx⟩ := childLabel_surjective O c d hr hd y.val
  exact ⟨⟨x.val,x.property,hx.symm ▸ y.property⟩,Subtype.ext hx⟩

/-- The disc-to-disc bijection in Lemma 3.34 induces a bijection between
the maximal children of the closed disc and of its proposed image. -/
theorem discToDisc_child_equiv [DenselyOrdered O.ValueGroup] (c d a b : K) {r s : O.ValueGroup}
    (hr : r ≠ 0) (hd : O.valuation d = r) (hs : s ≠ 0) (hb : O.valuation b = s)
    (W Z : Set (Residue O)) {f g : K → K} (hmap : DiscToDiscOn O
      (childLocus O c d hr hd W) (childLocus O a b hs hb Z) f g) :
    ∃ h : W ≃ Z, ∀ x : childLocus O c d hr hd W,
      h (labelOnLocus O c d hr hd W x) = labelOnLocus O a b hs hb Z ⟨f x.val,hmap.1.mapsTo x.property⟩ := by
  let A := childLocus O c d hr hd W
  let B := childLocus O a b hs hb Z
  let e : A ≃ B := hmap.1.equiv f
  apply quotient_equiv _ _ e (labelOnLocus_surjective O c d hr hd W) (labelOnLocus_surjective O a b hs hb Z)
  intro x y
  rw [Subtype.ext_iff,Subtype.ext_iff]
  exact (same_child_iff_share_open O c d hr hd W _ _ y.property.choose_spec).trans
    ((shareOpenSubdisc_image O hmap x.property y.property).trans
      (same_child_iff_share_open O a b hs hb Z ⟨(e x).val,(e x).property.choose⟩ ⟨(e y).val,(e y).property.choose⟩ (e y).property.choose_spec).symm)

variable [LinearOrder K] [IsStrictOrderedRing K] (hO : IsOrderConvex O)

/-- In the affine residue chart of its closed parent, either half thin
annulus is exactly the union of children on the corresponding open ray. -/
theorem childLocus_ray (a d : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : O.valuation d = r) (pos : 0 < d) (upper : Bool) :
    letI := residueLinearOrder O hO
    childLocus O a d hr hd (if upper then Ioi 0 else Iio 0) =
      annulusSide upper (openDisc O a r) (closedDisc O a r) := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let center : closedDisc O a r := ⟨a,mem_closedDisc_center O r a⟩
  have atZero : childLabel O a d hr hd center = 0 :=
    (discChildrenChart_eq_zero_iff O a d hr hd center).mpr (mem_openDisc_center O hr a)
  have openConv := valuativeDisc_ordConnected O hO a (Iio r) (fun _ _ huv hv => huv.trans_lt hv)
  have closedConv := valuativeDisc_ordConnected O hO a (Iic r) (fun _ _ huv hv => huv.trans hv)
  have centerIn := mem_openDisc_center O hr a
  ext x
  cases upper
  · change (∃ hx : x ∈ closedDisc O a r, childLabel O a d hr hd ⟨x,hx⟩ < 0) ↔
      (∃ b ∈ closedDisc O a r, b ≤ x) ∧ ∀ z ∈ openDisc O a r, x < z
    constructor
    · rintro ⟨hx,neg⟩
      rw [←atZero] at neg
      obtain ⟨hxlt,notIn⟩ := (discChildrenChart_lt_iff O hO a d hr hd pos ⟨x,hx⟩ center).mp neg
      exact ⟨⟨x,hx,le_rfl⟩,fun z hz => lt_of_not_ge (fun h => notIn (openConv.out hz centerIn ⟨h,hxlt.le⟩))⟩
    · rintro ⟨⟨b,hb,hl⟩,before⟩
      have small := before a centerIn
      let hx := closedConv.out hb center.property ⟨hl,small.le⟩
      refine ⟨hx,?_⟩
      rw [←atZero]
      exact (discChildrenChart_lt_iff O hO a d hr hd pos ⟨x,hx⟩ center).mpr
        ⟨small,fun h => (before x h).false⟩
  · change (∃ hx : x ∈ closedDisc O a r, 0 < childLabel O a d hr hd ⟨x,hx⟩) ↔
      (∀ z ∈ openDisc O a r, z < x) ∧ ∃ b ∈ closedDisc O a r, x ≤ b
    constructor
    · rintro ⟨hx,posx⟩
      rw [←atZero] at posx
      obtain ⟨hax,notIn⟩ := (discChildrenChart_lt_iff O hO a d hr hd pos center ⟨x,hx⟩).mp posx
      have out : x ∉ openDisc O a r := fun h => notIn ((openDisc_change_center O h).symm ▸ centerIn)
      exact ⟨fun z hz => lt_of_not_ge (fun h => out (openConv.out centerIn hz ⟨hax.le,h⟩)),⟨x,hx,le_rfl⟩⟩
    · rintro ⟨after,⟨b,hb,hh⟩⟩
      have big := after a centerIn
      let hx := closedConv.out center.property hb ⟨big.le,hh⟩
      refine ⟨hx,?_⟩
      rw [←atZero]
      exact (discChildrenChart_lt_iff O hO a d hr hd pos center ⟨x,hx⟩).mpr ⟨big,fun h =>
        (after x ((openDisc_change_center O h).symm ▸ mem_openDisc_center O hr x)).false⟩

end GeneralizedEuler.Section3
