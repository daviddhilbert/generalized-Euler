module

public import Section3.ValueGerms
public import Section2.SignedValue
import all Section2.WeakOminimal
import all Section2.SignedValue

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO in
/-- Lemma 3.9 in field and residue coordinates. A residue selection
meets every signed shell. Weak o-minimality bounds the partially met
shells, while orthogonality and the unary value cells stabilize both
ends. The two constants can differ. -/
theorem outer_disc_residue_germs [DenselyOrdered O.ValueGroup] (c : K) {r : O.ValueGroup} (hr : r ≠ 0)
    (f : K → Residue O) (select : Bool → O.ValueGroup → Residue O)
    (meets : ∀ b v, 0 < v → v < r → ∃ x : K, decide (x < 0) = b ∧ O.valuation x = v ∧ f (c+x) = select b v)
    (fieldCells : FiniteConvexUnion {x : K | 0 < O.valuation x ∧ O.valuation x < r ∧
      f (c+x) = select (decide (x < 0)) (O.valuation x)})
    (finiteValues : ∀ b, (select b '' Ioo 0 r).Finite)
    (valueCells : ∀ b z, z ∈ select b '' Ioo 0 r →
      FiniteConvexUnion {v ∈ Ioo 0 r | select b v = z}) :
    ∃ β, β ≠ 0 ∧ openDisc O c β ⊂ openDisc O c r ∧ ∃ u v : Residue O,
      (∀ x ∈ openDisc O c r \ openDisc O c β, x < c → f x = u) ∧
      (∀ x ∈ openDisc O c r \ openDisc O c β, c < x → f x = v) := by
  classical
  let key (x : K) := (decide (x < 0),O.valuation x)
  let shell (p : Bool × O.ValueGroup) := {x : K | key x = p}
  let chosen := {x : K | 0 < O.valuation x ∧ O.valuation x < r ∧ f (c+x) = select (key x).1 (key x).2}
  have same (x y : K) : key x = key y ↔ signedValuation O hO x = signedValuation O hO y := by
    let := rvLinearOrder O hO
    change key x = key y ↔ signedValue O hO (rv O x) = signedValue O hO (rv O y)
    rw [signedValue_eq_iff, unsignedValue_rv,unsignedValue_rv,rv_lt_zero_iff,rv_lt_zero_iff]
    simp only [key,Prod.mk.injEq,decide_eq_decide]
    exact and_comm
  have convex p : (shell p).OrdConnected := by
    by_cases ne : (shell p).Nonempty
    · obtain ⟨x,hx⟩ := ne
      have he : shell p = signedValuation O hO ⁻¹' {signedValuation O hO x} := by
        ext y; change key y = p ↔ signedValuation O hO y = _; rw [←same,show key x = p from hx]
      rw [he]; exact signedValuation_fiber_ordConnected O hO _
    · rw [not_nonempty_iff_eq_empty.mp ne]; infer_instance
  have cut := finite_cutLabels shell convex (fun i j ne => disjoint_left.mpr (fun x hx hy =>
    ne ((show key x = i from hx).symm.trans hy))) (show FiniteConvexUnion chosen from fieldCells)
  let exc := (cut.image Prod.snd).toFinset
  have agree (x : K) (hv : O.valuation x ∈ Ioo 0 r) (avoid : O.valuation x ∉ exc) :
      f (c+x) = select (key x).1 (key x).2 := by
    by_contra no
    obtain ⟨y,hb,hs,hy⟩ := meets (key x).1 (key x).2 hv.1 hv.2
    have eqn : key y = key x := Prod.ext hb hs
    have hcut : key x ∈ cutLabels shell chosen :=
      ⟨⟨y,eqn,hs ▸ hv.1,hs ▸ hv.2,by rwa [eqn]⟩,x,rfl,fun hm => no hm.2.2⟩
    exact avoid ((cut.image Prod.snd).mem_toFinset.mpr ⟨key x,hcut,rfl⟩)
  let R := O.ValueGroupᵒᵈ
  have exchange : Ioo (α := R) r 0 = (Ioo (0 : O.ValueGroup) r : Set O.ValueGroup) := by
    ext v; exact and_comm
  have fin (b) : (select b '' Ioo (α := R) r 0).Finite := exchange ▸ finiteValues b
  have cells (b z) (hz : z ∈ select b '' Ioo (α := R) r 0) :
      FiniteConvexUnion (X := R) {v ∈ Ioo (α := R) r 0 | select b v = z} := by
    rw [exchange] at hz ⊢
    obtain ⟨m,C,cv,eqn⟩ := valueCells b z hz
    exact ⟨m,C,fun j => (cv j).dual,eqn⟩
  obtain ⟨β',hβ,out,stable⟩ := stabilize_two_ends (G := R) (fun x => f (c+x)) O.valuation
    (fun x => (key x).1) select r 0 (pos_iff_ne_zero.mpr hr) fin cells exc
    (fun x h => agree x ⟨h.2,h.1⟩)
  let β : O.ValueGroup := OrderDual.ofDual β'
  have bpos : (0 : O.ValueGroup) < β := hβ.2
  have br : (β : O.ValueGroup) < r := hβ.1
  have proper : openDisc O c β ⊂ openDisc O c r := by
    refine ⟨fun x hx => (show O.valuation (x-c) < β from hx).trans br,?_⟩
    obtain ⟨d,hd⟩ := O.valuation_surjective β
    intro reverse
    have mem : d+c ∈ openDisc O c r := by change O.valuation (d+c-c) < r; simpa [hd] using br
    have fail := reverse mem
    change O.valuation (d+c-c) < β at fail
    simp [hd] at fail
  have atX (x : K) (h : x ∈ openDisc O c r \ openDisc O c β) : f x = out (decide (x-c < 0)) := by
    have s := stable (x-c) (show O.valuation (x-c) < r from h.1) (le_of_not_gt h.2)
    simpa only [add_sub_cancel, key] using s
  refine ⟨β,bpos.ne',proper,out true,out false,fun x hx lt => ?_,fun x hx lt => ?_⟩
  · simpa [sub_neg.mpr lt] using atX x hx
  · simpa [lt.not_gt] using atX x hx

end GeneralizedEuler.Section3
