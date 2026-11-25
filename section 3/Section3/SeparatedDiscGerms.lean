module

public import Section3.OuterDiscGerms
public import Section3.CofinalValues
import all Section2.WeakOminimal

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

private theorem finite_transversal {U V : Type*} {D : Set (U × V)} {L : Set U → Prop} {R : Set V → Prop}
    (sep : SeparatedSets L R D) :
    ∃ F : Finset V, ∀ u v, (u,v) ∈ D → ∃ w ∈ F, (u,w) ∈ D := by
  classical
  induction sep with
  | empty => exact ⟨∅,fun _ _ h => h.elim⟩
  | @insert A B D _ _ _ ih =>
    obtain ⟨F,hF⟩ := ih
    by_cases ne : B.Nonempty
    · obtain ⟨w,hw⟩ := ne
      refine ⟨insert w F,fun u v hv => ?_⟩
      rcases hv with hv | hv
      · exact ⟨w,Finset.mem_insert_self ..,Or.inl ⟨hv.1,hw⟩⟩
      · obtain ⟨w',mem,yes⟩ := hF _ _ hv
        exact ⟨w',Finset.mem_insert_of_mem mem,Or.inr yes⟩
    · rw [not_nonempty_iff_eq_empty.mp ne]; simpa using ⟨F,hF⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (O : ValuationSubring K) (hO : IsOrderConvex O)

abbrev positiveDiscSide (r : O.ValueGroup) := {z : K // 0 < z ∧ O.valuation z < r}

include hO in
private theorem constant_on_outer_side [DenselyOrdered O.ValueGroup] {r : O.ValueGroup} (hr : r ≠ 0)
    {V : Type*} (g : K → V)
    (sep : SeparatedSets (fun _ => True) (fun _ => True)
      (range fun x : positiveDiscSide O r => (O.valuation x.val,g x.val)))
    (cells : ∀ w, FiniteConvexUnion {x : positiveDiscSide O r | g x.val = w}) :
    ∃ b : positiveDiscSide O r, ∃ w, ∀ x : positiveDiscSide O r, b < x → g x.val = w := by
  classical
  let D := positiveDiscSide O r
  have atValue (v : O.ValueGroup) (pos : 0 < v) (lt : v < r) : ∃ x : D, O.valuation x.val = v := by
    obtain ⟨a,ha⟩ := O.valuation_surjective v
    have nz : a ≠ 0 := fun he => pos.ne' (by rw [←ha,he,map_zero])
    exact ⟨⟨|a|,abs_pos.mpr nz,by rwa [valuation_abs,ha]⟩,(valuation_abs O a).trans ha⟩
  obtain ⟨v,pv,vr⟩ := exists_between (pos_iff_ne_zero.mpr hr)
  let : Nonempty D := ⟨(atValue v pv vr).choose⟩
  obtain ⟨F,hit⟩ := finite_transversal sep
  have unbounded : ¬ BddAbove (⋃ w ∈ (F : Set V), {x : D | g x.val = w}) := by
    rintro ⟨b,hb⟩
    obtain ⟨s,bs,sr⟩ := exists_between b.property.2
    obtain ⟨a,ha⟩ := atValue s (zero_le.trans_lt bs) sr
    obtain ⟨w,hw,z,hz⟩ := hit _ _ (mem_range_self a)
    have zval := (congrArg Prod.fst hz).trans ha
    have zle := hb (mem_iUnion₂.mpr ⟨w,hw,show g z.val = w from congrArg Prod.snd hz⟩)
    exact bs.not_ge (zval ▸ valuation_le_of_nonneg_le O hO z.property.1.le (show z.val ≤ b.val from zle))
  have some : ∃ w ∈ F, ¬ BddAbove {x : D | g x.val = w} := by
    by_contra! allBound
    exact unbounded (F.finite_toSet.bddAbove_biUnion.mpr allBound)
  obtain ⟨w,_,hw⟩ := some
  obtain ⟨b,hb⟩ := tail_of_unbounded_convex_union (cells w) hw
  exact ⟨b,w,hb⟩

include hO in
/-- Lemma 3.9 directly from residue–value orthogonality and weak o-minimality.
A finite collection of residues meets every shell on a given side. One residue
then occurs cofinally and its unary fiber contains an entire end. -/
theorem outer_disc_germs_of_separation [DenselyOrdered O.ValueGroup] {r : O.ValueGroup} (hr : r ≠ 0)
    (c : K) (f : K → Residue O)
    (sep : ∀ b : Bool, SeparatedSets (fun _ => True) (fun _ => True)
      (range fun x : positiveDiscSide O r => (O.valuation x.val,f (if b then c-x.val else c+x.val))))
    (cells : ∀ (b : Bool) w, FiniteConvexUnion {x : positiveDiscSide O r | f (if b then c-x.val else c+x.val) = w}) :
    ∃ β, β ≠ 0 ∧ openDisc O c β ⊂ openDisc O c r ∧ ∃ u v : Residue O,
      (∀ x ∈ openDisc O c r \ openDisc O c β, x < c → f x = u) ∧
      (∀ x ∈ openDisc O c r \ openDisc O c β, c < x → f x = v) := by
  choose b w tail using fun side => constant_on_outer_side O hO hr
    (fun z => f (if side then c-z else c+z)) (sep side) (cells side)
  obtain ⟨β,hβ,br⟩ := exists_between (max_lt (b true).property.2 (b false).property.2)
  have pb := zero_le.trans_lt ((le_max_left _ _).trans_lt hβ)
  have proper : openDisc O c β ⊂ openDisc O c r := by
    refine ⟨fun x hx => (show O.valuation (x-c) < β from hx).trans br,?_⟩
    obtain ⟨d,hd⟩ := O.valuation_surjective β
    intro rev
    have mem : d+c ∈ openDisc O c r := by change O.valuation (d+c-c) < r; simpa [hd] using br
    have fail := rev mem
    change O.valuation (d+c-c) < β at fail
    simp [hd] at fail
  have past (s : Bool) (z : positiveDiscSide O r) (hz : β ≤ O.valuation z.val) : b s < z := by
    apply lt_of_not_ge
    intro le
    have small := (valuation_le_of_nonneg_le O hO z.property.1.le (show z.val ≤ (b s).val from le))
    have bs : O.valuation (b s).val < β := by
      cases s
      · exact (le_max_right _ _).trans_lt hβ
      · exact (le_max_left _ _).trans_lt hβ
    exact bs.not_ge (hz.trans small)
  refine ⟨β,pb.ne',proper,w true,w false,?_,?_⟩
  · intro x hx less
    have valEq : O.valuation (c-x) = O.valuation (x-c) := by rw [←neg_sub x c,O.valuation.map_neg]
    let z : positiveDiscSide O r := ⟨c-x,sub_pos.mpr less,valEq ▸ hx.1⟩
    have hz : β ≤ O.valuation z.val := valEq ▸ le_of_not_gt hx.2
    simpa [z] using tail true z (past true z hz)
  · intro x hx less
    let z : positiveDiscSide O r := ⟨x-c,sub_pos.mpr less,hx.1⟩
    simpa [z] using tail false z (past false z (le_of_not_gt hx.2))

end GeneralizedEuler.Section3
