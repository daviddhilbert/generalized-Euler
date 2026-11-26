module

public import Section4.IntervalScales
public import Section4.DefinableValueFrames
public import Mathlib.Order.Interval.Set.OrderIso

/-! The two affine formulas identifying bounded intervals of comparable
width. Only constants from the base and slopes in the exponent field occur. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

def brokenLine (c d : F) (t x : V) := if x ≤ t then c • x else c • t + d • (x-t)

omit [IsStrictOrderedRing F] in
theorem brokenLine_strictMono {c d : F} (hc : 0 < c) (hd : 0 < d) (t : V) :
    StrictMono (brokenLine c d t) := by
  intro x y h
  unfold brokenLine
  split_ifs with hx hy hy
  · exact smul_lt_smul_of_pos_left h hc
  · exact (smul_le_smul_of_nonneg_left hx hc.le).trans_lt
      (lt_add_of_pos_right _ (smul_pos hd (sub_pos.mpr (lt_of_not_ge hy))))
  · exact (hx (h.le.trans hy)).elim
  · exact add_lt_add_right (smul_lt_smul_of_pos_left (sub_lt_sub_right h t) hd) _

def brokenLineOrderIso {c d : F} (hc : 0 < c) (hd : 0 < d) (t : V) : V ≃o V :=
  StrictMono.orderIsoOfSurjective _ (brokenLine_strictMono hc hd t) (by
    intro y
    by_cases h : y ≤ c • t
    · refine ⟨c⁻¹ • y,?_⟩
      have hx := smul_le_smul_of_nonneg_left h (inv_nonneg.mpr hc.le)
      rw [inv_smul_smul₀ hc.ne'] at hx
      simp [brokenLine,hx,smul_inv_smul₀ hc.ne']
    · refine ⟨t + d⁻¹ • (y - c • t),?_⟩
      have hy := smul_pos (inv_pos.mpr hd) (sub_pos.mpr (lt_of_not_ge h))
      have hx := (lt_add_of_pos_right t hy).not_ge
      simp [brokenLine,hx,smul_inv_smul₀ hd.ne'])

def intervalKnot (c d : F) (a b : V) : V := (d-c)⁻¹ • (d • a - b)

theorem intervalKnot_inside {c d : F} {a b : V} (hcd : c < d) (lo : c • a < b) (hi : b < d • a) :
    0 < intervalKnot c d a b ∧ intervalKnot c d a b < a := by
  have pos := sub_pos.mpr hcd
  refine ⟨smul_pos (inv_pos.mpr pos) (sub_pos.mpr hi),?_⟩
  apply (smul_lt_smul_iff_of_pos_left pos).mp
  rw [intervalKnot,smul_inv_smul₀ pos.ne',sub_smul]
  exact sub_lt_sub_left lo _

theorem brokenLine_endpoints {c d : F} {a b : V} (hcd : c < d) (lo : c • a < b) (hi : b < d • a) :
    brokenLine c d (intervalKnot c d a b) 0 = 0 ∧ brokenLine c d (intervalKnot c d a b) a = b := by
  let t := intervalKnot c d a b
  obtain ⟨left,right⟩ := intervalKnot_inside hcd lo hi
  refine ⟨by simp [brokenLine,left.le],?_⟩
  have ht : (d-c) • t = d • a - b := smul_inv_smul₀ (sub_ne_zero.mpr hcd.ne') _
  rw [sub_smul] at ht
  simp only [brokenLine,ite_eq_right right.not_ge,smul_sub]
  change c • t + (d • a - d • t) = b
  calc c • t + (d • a - d • t) = d • a - (d • t - c • t) := by abel
       _ = b := by rw [ht]; abel

theorem scale_slopes {a b : V} (ha : 0 < a) (hb : 0 < b)
    (hab : a ∈ scaleSpace F b) (hba : b ∈ scaleSpace F a) :
    ∃ c d : F, 0 < c ∧ c < d ∧ c • a < b ∧ b < d • a := by
  obtain ⟨u,hu,hua⟩ := (mem_scaleSpace_iff F hb).mp hab
  obtain ⟨v,hv,hvb⟩ := (mem_scaleSpace_iff F ha).mp hba
  rw [abs_of_pos ha] at hua
  rw [abs_of_pos hb] at hvb
  let c := (u+1)⁻¹
  let d := v+1
  have cp : 0 < c := inv_pos.mpr (by positivity)
  have lo : c • a < b := by
    apply (smul_lt_smul_iff_of_pos_left (show 0 < u+1 by positivity)).mp
    rw [show (u+1) • c • a = a from smul_inv_smul₀ (by positivity) a,add_smul,one_smul]
    exact hua.trans_lt (lt_add_of_pos_right _ hb)
  have hi : b < d • a := by
    change b < (v+1) • a
    rw [add_smul,one_smul]
    exact hvb.trans_lt (lt_add_of_pos_right _ ha)
  exact ⟨c,d,cp,lt_of_not_ge (fun h => (lo.trans hi).not_ge (smul_le_smul_of_nonneg_right h ha.le)),lo,hi⟩


/-- The interval identification extends to an order isomorphism of the
line whose graph is definable over the same value subspace. -/
theorem comparable_widths_definable {J : Language} [J.Structure V] (G : Submodule F V)
    (lang : ValueLanguage (J := J) G)
    (leDef : ∀ t ∈ G, (G : Set V).Definable J {x : Unit → V | x () ≤ t})
    {a b : V} (aG : a ∈ G) (bG : b ∈ G) (ha : 0 < a) (hb : 0 < b)
    (ab : a ∈ scaleSpace F b) (ba : b ∈ scaleSpace F a) :
    ∃ e : V ≃o V, e '' Set.Ioo 0 a = Set.Ioo 0 b ∧
      (G : Set V).DefinableFun J (fun x : Unit → V => e (x ())) := by
  obtain ⟨c,d,hc,hcd,lo,hi⟩ := scale_slopes ha hb ab ba
  let t := intervalKnot c d a b
  let e := brokenLineOrderIso hc (hc.trans hcd) t
  obtain ⟨ez,ea⟩ := brokenLine_endpoints hcd lo hi
  have eq (x : V) : e x = brokenLine c d t x := rfl
  refine ⟨e,by rw [OrderIso.image_Ioo,eq,eq,ez,ea],?_⟩
  have ht : t ∈ G := G.smul_mem _ (G.sub_mem (G.smul_mem _ aG) bG)
  have shift : (G : Set V).DefinableFun J (fun x : Unit → V => x () - t) := by
    simpa only [sub_eq_add_neg] using lang.addFun (Set.DefinableFun.proj J (i := ()))
      (J.definableFun_const Unit (G.neg_mem ht))
  have right := lang.addFun (J.definableFun_const Unit (G.smul_mem c ht))
    ((lang.smul d).comp (g := fun x _ => x () - t) (fun _ => shift))
  exact Set.DefinableFun.ite (leDef t ht) (lang.smul c) right

end GeneralizedEuler.Section4
