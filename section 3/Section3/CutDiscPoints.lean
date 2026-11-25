module

public import Section2.EndDiscs
public import Section2.DiscCodes
import all Section2.DiscCodes
public import Section3.DefinablePoints

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem endDisc_hasCode {E : Set K} (h : IsEndDisc O E) :
    ∃ e : DiscCode O, e.points O = E := by
  rcases h with ⟨c,rfl⟩ | ⟨c,r,hr,rfl | rfl⟩
  · exact ⟨closedDiscCode O c 0, closedDiscCode_zero_points O c⟩
  · exact ⟨openDiscCode O c r hr,openDiscCode_points O c r hr⟩
  · exact ⟨closedDiscCode O c r,closedDiscCode_points O c r⟩

include hO

theorem discCode_ordConnected (d : DiscCode O) : (d.points O).OrdConnected := by
  induction d using Quotient.inductionOn with
  | h desc =>
    cases desc with
    | openDisc c r hr =>
      change ((openDiscCode O c r hr).points O).OrdConnected
      rw [openDiscCode_points]
      exact valuativeDisc_ordConnected O hO c (Iio r) (fun _ _ h h' => h.trans_lt h')
    | closedDisc c r =>
      change ((closedDiscCode O c r).points O).OrdConnected
      rw [closedDiscCode_points]
      exact valuativeDisc_ordConnected O hO c (Iic r) (fun _ _ h h' => h.trans h')

/-- If an endpoint test distinguishes two points of a disc, its end disc
lies strictly inside that disc. This treats included and excluded ends. -/
theorem proper_end_of_ray_cut (d : DiscCode O) (e : ValuativeIntervalEnd (K := K))
    (he : IsEndDisc O e.disc) (hne : ¬ e.disc ⊂ d.points O) {x y : K}
    (hx : x ∈ d.points O) (hy : y ∈ d.points O) :
    (allowedAbove (some e) x ↔ allowedAbove (some e) y) ∧
    (allowedBelow (some e) x ↔ allowedBelow (some e) y) := by
  obtain ⟨c,hc⟩ := endDisc_hasCode O he
  by_cases hd : Disjoint (d.points O) e.disc
  · have forb {z} (hz : z ∈ e.disc) : z ∉ d.points O := fun h => Set.disjoint_left.mp hd h hz
    have same (z : K) (hz : z ∈ e.disc) :
        (z ≤ x ↔ z ≤ y) ∧ (x ≤ z ↔ y ≤ z) := by
      have conv := discCode_ordConnected O hO d
      constructor <;> constructor
      · intro h; by_contra! h'; exact forb hz (conv.out hy hx ⟨h'.le,h⟩)
      · intro h; by_contra! h'; exact forb hz (conv.out hx hy ⟨h'.le,h⟩)
      · intro h; by_contra! h'; exact forb hz (conv.out hx hy ⟨h,h'.le⟩)
      · intro h; by_contra! h'; exact forb hz (conv.out hy hx ⟨h,h'.le⟩)
    cases e with
    | mk E inc =>
      cases inc <;> simp only [allowedAbove,allowedBelow]
      · constructor <;> apply forall_congr' <;> intro z <;> apply forall_congr' <;> intro hz
        · exact lt_iff_lt_of_le_iff_le' (same z hz).2 (same z hz).1
        · exact lt_iff_lt_of_le_iff_le' (same z hz).1 (same z hz).2
      · constructor <;> apply exists_congr <;> intro z <;> apply and_congr_right <;> intro hz
        · exact (same z hz).1
        · exact (same z hz).2
  · obtain ⟨z,hzd,hze⟩ := Set.not_disjoint_iff.mp hd
    have hnest := DiscCode.nested_of_mem_both O hzd (hc.symm ▸ hze)
    rw [hc] at hnest
    have hsub : d.points O ⊆ e.disc := by
      rcases hnest with h | h
      · exact h
      · by_contra hfalse; exact hne ⟨h,hfalse⟩
    have hxe := hsub hx
    have hye := hsub hy
    cases e with
    | mk E inc =>
      cases inc <;> simp only [allowedAbove,allowedBelow]
      · exact ⟨iff_of_false (fun h => (h x hxe).false) (fun h => (h y hye).false),
          iff_of_false (fun h => (h x hxe).false) (fun h => (h y hye).false)⟩
      · exact ⟨iff_of_true ⟨x,hxe,le_rfl⟩ ⟨y,hye,le_rfl⟩,
          iff_of_true ⟨x,hxe,le_rfl⟩ ⟨y,hye,le_rfl⟩⟩

/-- A cut in a finite HNF union witnesses a proper end disc. A point of a
definable closed disc inside that end's parent is therefore a point in d.
The base is the ordinary two-sorted base of 3.20–3.21. -/
theorem cut_disc_meets_base {I : Type*} (d : DiscCode O) (A F : Set K)
    (lo hi : I → Option (ValuativeIntervalEnd (K := K)))
    (hA : A = ⋃ j, valuativeInterval (lo j) (hi j))
    (ends : ∀ j e, e ∈ lo j ∨ e ∈ hi j → IsEndDisc O e.disc)
    (point : ∀ j e, e ∈ lo j ∨ e ∈ hi j → e.disc ⊂ d.points O → (F ∩ d.points O).Nonempty)
    (hc : ((d.points O) ∩ A).Nonempty) (hm : ((d.points O) \ A).Nonempty) :
    (F ∩ d.points O).Nonempty := by
  obtain ⟨x,hxd,hx⟩ := hc
  obtain ⟨y,hyd,hy⟩ := hm
  rw [hA] at hx hy
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
  by_contra hn
  have tests (e : ValuativeIntervalEnd (K := K)) (h : e ∈ lo j ∨ e ∈ hi j) :=
    proper_end_of_ray_cut O hO d e (ends j e h) (fun hlt => hn (point j e h hlt)) hxd hyd
  apply hy
  apply Set.mem_iUnion.mpr
  refine ⟨j,?_,?_⟩
  · have h := hj.1
    cases he : lo j with
    | none => trivial
    | some e =>
      have ht := (tests e (Or.inl (by simp [he]))).1
      rw [he] at h
      exact ht.mp h
  · have h := hj.2
    cases he : hi j with
    | none => trivial
    | some e =>
      have ht := (tests e (Or.inr (by simp [he]))).2
      rw [he] at h
      exact ht.mp h

omit [LinearOrder K] [IsStrictOrderedRing K] hO in
/-- When the proper end is open, its closed disc of the same radius is
still in the ambient disc. No center has to be named in the fixed base. -/
theorem closed_parent_subset_of_proper_open [DenselyOrdered O.ValueGroup]
    (d : DiscCode O) {a : K} {r : O.ValueGroup} (hr : r ≠ 0)
    (h : openDisc O a r ⊂ d.points O) : closedDisc O a r ⊆ d.points O := by
  induction d using Quotient.inductionOn with
  | h descr =>
    cases descr with
    | closedDisc c s => exact closedDisc_minimal_parent O hr h.1
    | openDisc c s hs =>
      have hac : a ∈ openDisc O c s := h.1 (mem_openDisc_center O hr a)
      change openDisc O a r ⊂ openDisc O c s at h
      change closedDisc O a r ⊆ openDisc O c s
      rw [← openDisc_change_center O hac] at h ⊢
      have hrs : r < s := lt_of_not_ge (fun hsr => h.2 (fun _ hx => lt_of_lt_of_le hx hsr))
      exact fun x hx => (show O.valuation (x-a) ≤ r from hx).trans_lt hrs

end GeneralizedEuler.Section3
