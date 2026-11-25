module

public import Section3.ConvexCuts
public import Section3.Atomicity
public import Section2.DiscCodes
public import Mathlib.Data.Set.Finite.Lattice

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem fixed_radius_disjoint {I : Type*} (c : I → K) (r : O.ValueGroup)
    (hinj : Function.Injective (fun i => openDisc O (c i) r)) :
    ∀ i j, i ≠ j → Disjoint (openDisc O (c i) r) (openDisc O (c j) r) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun x hx hy => hij
    (hinj ((openDisc_change_center O hx).symm.trans (openDisc_change_center O hy))))

/-- Lemma 3.22. The labels index distinct discs in A. The saturation premise
realizes a small family of tests on the labels when all its finite subfamilies
are realized. The tests are precisely the base-and-radius formulas. -/
theorem exists_atomic_openDisc {I : Type*} [Infinite I] (c : I → K)
    (hO : IsOrderConvex O) (r : O.ValueGroup) (hr : r ≠ 0)
    (hinj : Function.Injective (fun i => openDisc O (c i) r))
    (D : Set (Set K)) (hHNF : ∀ B ∈ D, FiniteConvexUnion B)
    (hsat : let cuts := cutLabels (fun i => openDisc O (c i) r)
      (∀ F : Finset D, ∃ i, ∀ B ∈ F, i ∉ cuts B.val) →
        ∃ i, ∀ B : D, i ∉ cuts B.val)
    (named : I → Set (Set K))
    (hdef : ∀ i, openDisc O (c i) r ∈ named i)
    (hcode : ∀ i B, B ∈ named i → ∃ C ∈ D, ∀ x ∈ openDisc O (c i) r, x ∈ B ↔ x ∈ C) :
    ∃ i, AtomicOver (named i) (openDisc O (c i) r) := by
  let discs i := openDisc O (c i) r
  have hfin (B : D) : (cutLabels discs B.val).Finite :=
    finite_cutLabels discs (fun i => valuativeDisc_ordConnected O hO (c i) (Set.Iio r)
      (fun _ _ hab hb => hab.trans_lt hb)) (fixed_radius_disjoint O c r hinj) (hHNF _ B.property)
  obtain ⟨i, hi⟩ := hsat (by
    intro F
    have hU := F.finite_toSet.biUnion (fun B _ => hfin B)
    obtain ⟨i, _, hin⟩ := (Set.infinite_univ (α := I)).exists_notMem_finite hU
    exact ⟨i, fun B hB hc => hin (Set.mem_iUnion₂.mpr ⟨B, hB, hc⟩)⟩)
  refine ⟨i, hdef i, GeneratesType.of_same_traces ?_ (hcode i)⟩
  refine ⟨⟨c i, mem_openDisc_center O hr _⟩, ?_⟩
  intro B hB x hx y hy
  have H := hi ⟨B,hB⟩
  constructor
  · intro h
    by_contra h'
    exact H ⟨⟨x, hx, h⟩, y, hy, h'⟩
  · intro h
    by_contra h'
    exact H ⟨⟨y, hy, h⟩, x, hx, h'⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Substitution that supplies the added-code trace in Lemma 3.22. -/
theorem centered_code_trace {c : K} {r : O.ValueGroup} (hr : r ≠ 0)
    (test : K → DiscCode O → Prop) :
    ∀ x ∈ openDisc O c r,
      test x (openDiscCode O c r hr) ↔ test x (openDiscCode O x r hr) := by
  intro x hx
  rw [openDiscCode_change_center O hr hx]

end GeneralizedEuler.Section3
