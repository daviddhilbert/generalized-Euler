module

public import Section2.FieldDefinableClosure
public import Section2.PowerBounded
public import Section2.ResidueInterpretation
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Tactic.Linarith

/-! The continuous-function presentation in Remark 2.3. Distances
to definable sets use definable completeness of the ordered field. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language Set Filter
open scoped Topology

universe u v

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem IsUnaryCell.exists_isGLB {C : Set K} (hC : IsUnaryCell C)
    (hne : C.Nonempty) (hbelow : BddBelow C) : ∃ a, IsGLB C a := by
  rcases hC with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · obtain ⟨x, hx⟩ := hbelow
    obtain ⟨y, hy⟩ := exists_lt x
    exact (hy.not_ge (hx (Set.mem_univ y))).elim
  · exact ⟨a, isGLB_singleton⟩
  · obtain ⟨x, hx⟩ := hbelow
    obtain ⟨y, hy⟩ := exists_lt (min x a)
    exact ((hy.trans_le (min_le_left _ _)).not_ge (hx (hy.trans_le (min_le_right _ _)))).elim
  · exact ⟨a, isGLB_Ioi⟩
  · obtain ⟨c, hc⟩ := hne
    exact ⟨a, isGLB_Ioo (hc.1.trans hc.2)⟩

private theorem exists_isGLB_of_finite_unaryCells (C : Finset (Set K))
    (hCells : ∀ c ∈ C, IsUnaryCell c) (hne : (⋃ c ∈ C, c).Nonempty)
    (hbelow : BddBelow (⋃ c ∈ C, c)) : ∃ a, IsGLB (⋃ c ∈ C, c) a := by
  classical
  induction C using Finset.induction_on with
  | empty => simp at hne
  | @insert c C hc ih =>
    simp only [Finset.set_biUnion_insert] at hne hbelow ⊢
    by_cases h : c.Nonempty
    · obtain ⟨a, ha⟩ := (hCells c (Finset.mem_insert_self _ _)).exists_isGLB h
        (hbelow.mono Set.subset_union_left)
      by_cases ht : (⋃ d ∈ C, d).Nonempty
      · obtain ⟨b, hb⟩ := ih (fun d hd => hCells d (Finset.mem_insert_of_mem hd)) ht
          (hbelow.mono Set.subset_union_right)
        exact ⟨a ⊓ b, ha.union hb⟩
      · rw [Set.not_nonempty_iff_eq_empty.mp ht, Set.union_empty]
        exact ⟨a, ha⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp h, Set.empty_union] at hne hbelow ⊢
      exact ih (fun d hd => hCells d (Finset.mem_insert_of_mem hd)) hne hbelow

/-- O-minimality gives an infimum for each nonempty bounded-below
definable unary set, including over a non-Archimedean field. -/
theorem IsOMinimal.exists_isGLB {L : Language.{u, v}} [L.Structure K] (h : IsOMinimal (K := K) L)
    {D : Set K} (hD : (Set.univ : Set K).Definable₁ L D) (hne : D.Nonempty)
    (hbelow : BddBelow D) : ∃ a, IsGLB D a := by
  obtain ⟨C, hC, rfl⟩ := h D hD
  exact exists_isGLB_of_finite_unaryCells C hC hne hbelow

section Distance

variable {I : Type*} [Finite I]

/-- Positive radii of open coordinate boxes meeting the set. -/
def boxRadii (D : Set (I → K)) (x : I → K) : Set K :=
  {r | 0 < r ∧ ∃ y ∈ D, ∀ i, |x i - y i| < r}

theorem boxRadii_nonempty {D : Set (I → K)} (hD : D.Nonempty) (x : I → K) :
    (boxRadii D x).Nonempty := by
  obtain ⟨y, hy⟩ := hD
  obtain ⟨b, hb⟩ := (Set.finite_range (fun i => |x i - y i|)).bddAbove
  obtain ⟨r, hr⟩ := exists_gt (max b 0)
  exact ⟨r, (le_max_right _ _).trans_lt hr, y, hy,
    fun i => (hb (Set.mem_range_self i)).trans_lt ((le_max_left _ _).trans_lt hr)⟩

omit [IsStrictOrderedRing K] [Finite I] in
theorem boxRadii_bddBelow (D : Set (I → K)) (x : I → K) : BddBelow (boxRadii D x) :=
  ⟨0, fun _ hr => hr.1.le⟩

omit [Finite I] in
private theorem distance_le_add_of_box {D : Set (I → K)} {d : (I → K) → K}
    (hd : ∀ x, IsGLB (boxRadii D x) (d x)) {x y : I → K} {ε : K}
    (hε : 0 < ε) (hxy : ∀ i, |x i - y i| < ε) : d x ≤ d y + ε := by
  apply sub_le_iff_le_add.mp
  apply (le_isGLB_iff (hd y)).mpr
  rintro r ⟨hr, z, hz, hyz⟩
  apply sub_le_iff_le_add.mpr
  apply (hd x).1
  refine ⟨add_pos hr hε, z, hz, fun i => ?_⟩
  exact (abs_sub_le _ _ _).trans_lt (by
    rw [add_comm r ε]
    exact add_lt_add (hxy i) (hyz i))

variable [TopologicalSpace K] [OrderTopology K]

private theorem mem_nhds_box (x : I → K) {ε : K} (hε : 0 < ε) :
    {y | ∀ i, |x i - y i| < ε} ∈ 𝓝 x := by
  have hEq : {y | ∀ i, |x i - y i| < ε} =
      Set.pi Set.univ (fun i => Set.Ioo (x i - ε) (x i + ε)) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    refine forall_congr' fun i => ?_
    rw [abs_lt]
    constructor <;> intro h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  rw [hEq]
  exact (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).mem_nhds
    (fun _ _ => ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩)

omit [TopologicalSpace K] [OrderTopology K] in
private theorem exists_pos_le_all (f : I → K) (hf : ∀ i, 0 < f i) :
    ∃ ε, 0 < ε ∧ ∀ i, ε ≤ f i := by
  classical
  let := Fintype.ofFinite I
  let C := insert 1 (Finset.univ.image f)
  have hC : C.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨C.min' hC, ?_, fun i => Finset.min'_le C _ ?_⟩
  · have hm := C.min'_mem hC
    rcases Finset.mem_insert.mp hm with he | hi
    · rw [he]
      exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hi
      exact hi ▸ hf i
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem exists_box_subset_of_mem_nhds {x : I → K} {V : Set (I → K)} (hV : V ∈ 𝓝 x) :
    ∃ ε, 0 < ε ∧ {y | ∀ i, |x i - y i| < ε} ⊆ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨J, _, U, hU, hsub⟩ := hV
  choose a b hab hI using fun i => mem_nhds_iff_exists_Ioo_subset.mp (hU i)
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_all (fun i => min (x i - a i) (b i - x i))
    (fun i => lt_min (sub_pos.mpr (hab i).1) (sub_pos.mpr (hab i).2))
  refine ⟨ε, hε, fun y hy => hsub (fun i _ => hI i ?_)⟩
  have h₁ := (hle i).trans (min_le_left _ _)
  have h₂ := (hle i).trans (min_le_right _ _)
  have h₃ := abs_lt.mp (hy i)
  exact ⟨by linarith [h₁, h₃.2], by linarith [h₂, h₃.1]⟩

/-- Distances obtained from the box-radius infima are continuous in
the product of the order topologies. -/
theorem continuous_of_isGLB_boxRadii {D : Set (I → K)} {d : (I → K) → K}
    (hd : ∀ x, IsGLB (boxRadii D x) (d x)) : Continuous d := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε := (d x - a) / 2
    have hε : 0 < ε := half_pos (sub_pos.mpr ha)
    filter_upwards [mem_nhds_box x hε] with y hy
    have h := distance_le_add_of_box hd hε hy
    change 0 < (d x - a) / 2 at hε
    dsimp [ε] at h
    linarith
  · intro b hb
    let ε := (b - d x) / 2
    have hε : 0 < ε := half_pos (sub_pos.mpr hb)
    filter_upwards [mem_nhds_box x hε] with y hy
    have hxy (i : I) : |y i - x i| < ε := by
      rw [abs_sub_comm]
      exact hy i
    have h := distance_le_add_of_box hd hε hxy
    change 0 < (b - d x) / 2 at hε
    dsimp [ε] at h
    linarith

/-- The zero set of the distance to a nonempty set is its closure. -/
theorem isGLB_boxRadii_eq_zero_iff_mem_closure {D : Set (I → K)} {x : I → K} {a : K}
    (ha : IsGLB (boxRadii D x) a) : a = 0 ↔ x ∈ closure D := by
  constructor
  · intro hz
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨ε, hε, hsub⟩ := exists_box_subset_of_mem_nhds hV
    obtain ⟨r, hr, _, hlt⟩ := ha.exists_between (hz.symm ▸ hε)
    obtain ⟨_, y, hy, hbox⟩ := hr
    exact ⟨y, hsub (fun i => (hbox i).trans hlt), hy⟩
  · intro hx
    have h0 : 0 ≤ a := (le_isGLB_iff ha).mpr (fun _ hr => hr.1.le)
    apply le_antisymm _ h0
    by_contra! han
    obtain ⟨y, hy, hyD⟩ := mem_closure_iff_nhds.mp hx _ (mem_nhds_box x (half_pos han))
    have h := ha.1 (show a / 2 ∈ boxRadii D x from ⟨half_pos han, y, hyD, hy⟩)
    linarith

end Distance

section Definability

variable {L : Language.{u, v}} [L.Structure K] {A : Set K}
  (F : OrderedFieldTerms L) (hF : InterpretsOrderedFieldTerms F (A := K))

include hF

omit [IsStrictOrderedRing K] in
private theorem definable_le_of_definableFunctions {I : Type*} {f g : (I → K) → K}
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.Definable L {x | f x ≤ g x} := by
  have hRel : A.Definable L {x : Fin 2 → K | x 0 ≤ x 1} := by
    rw [Set.definable_iff_exists_formula_sum]
    refine ⟨F.le.formula (fun i => .var (.inr i)), ?_⟩
    ext x
    exact (hF.le x).symm
  have hMap : A.DefinableMap L (fun x => ![f x, g x]) := by
    intro i
    fin_cases i <;> assumption
  exact hRel.preimage_map hMap

omit [IsStrictOrderedRing K] in
private theorem definable_lt_of_definableFunctions {I : Type*} {f g : (I → K) → K}
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.Definable L {x | f x < g x} := by
  simpa only [Set.compl_ofPred, not_le] using (definable_le_of_definableFunctions F hF hg hf).compl

omit [IsStrictOrderedRing K] in
private theorem definable_sub_of_definableFunctions {I : Type*} {f g : (I → K) → K}
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.DefinableFun L (fun x => f x - g x) := by
  have hMap : A.DefinableMap L (fun x => ![f x, g x]) := by
    intro i
    fin_cases i <;> assumption
  have h := (F.sub.definableFun_realize.of_empty (A := A)).comp hMap
  simpa only [hF.sub, Matrix.cons_val_zero, Matrix.cons_val_one] using h

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] hF in
private theorem definable_forall_scalar {I : Type*} {P : (I → K) → K → Prop}
    (hP : A.Definable L {u : I ⊕ Unit → K | P (u ∘ Sum.inl) (u (.inr ()))}) :
    A.Definable L {x | ∀ r, P x r} := by
  convert hP.forall_of_finite using 1
  ext x
  constructor
  · intro h r
    exact h (r ())
  · intro h r
    exact h (fun _ => r)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] hF in
private theorem definable_const_of_closed_term {I : Type*} (t : L.Term Empty) (b : K)
    (ht : t.realize (Empty.elim : Empty → K) = b) : A.DefinableFun L (fun _ : I → K => b) := by
  have h := (t.relabel (Empty.elim : Empty → I)).definableFun_realize (M := K)
  have hEq (v : I → K) : t.realize (v ∘ Empty.elim) = b :=
    Subsingleton.elim (v ∘ Empty.elim) (Empty.elim : Empty → K) ▸ ht
  simpa only [Term.realize_relabel, hEq] using h.of_empty (A := A)

variable {I : Type*} [Finite I]

private theorem definable_boxRadii_relation {D : Set (I → K)} (hD : A.Definable L D) :
    A.Definable L {v : Option I → K | v none ∈ boxRadii D (v ∘ some)} := by
  let W := (Option I ⊕ I) → K
  have hz : A.DefinableFun L (fun _ : W => (0 : K)) :=
    definable_const_of_closed_term F.zero 0 hF.zero
  have hpos : A.Definable L {u : W | 0 < u (.inl none)} :=
    definable_lt_of_definableFunctions F hF hz (Set.DefinableFun.proj L)
  have hcoord (i : I) : A.Definable L {u : W | |u (.inl (some i)) - u (.inr i)| < u (.inl none)} := by
    let x : W → K := fun u => u (.inl (some i))
    let y : W → K := fun u => u (.inr i)
    let r : W → K := fun u => u (.inl none)
    have hx : A.DefinableFun L x := (Set.DefinableFun.proj L)
    have hy : A.DefinableFun L y := (Set.DefinableFun.proj L)
    have hr : A.DefinableFun L r := (Set.DefinableFun.proj L)
    have h₁ := definable_lt_of_definableFunctions F hF (definable_sub_of_definableFunctions F hF hx hy) hr
    have h₂ := definable_lt_of_definableFunctions F hF (definable_sub_of_definableFunctions F hF hy hx) hr
    convert h₂.inter h₁ using 1
    ext u
    change |x u - y u| < r u ↔ y u - x u < r u ∧ x u - y u < r u
    rw [abs_lt, ← neg_sub, neg_lt_neg_iff]
  have hAll : A.Definable L {u : W | ∀ i, |u (.inl (some i)) - u (.inr i)| < u (.inl none)} := by
    convert Set.definable_iInter_of_finite hcoord using 1
    ext u
    rw [Set.mem_iInter]
    rfl
  have hW := (hpos.inter (hD.preimage_comp Sum.inr)).inter hAll
  convert hW.exists_of_finite using 1
  ext v
  change (0 < v none ∧ ∃ y ∈ D, ∀ i, |v (some i) - y i| < v none) ↔ _
  exact ⟨fun ⟨hr, y, hy, hb⟩ => ⟨y, ⟨hr, hy⟩, hb⟩,
    fun ⟨y, ⟨hr, hy⟩, hb⟩ => ⟨hr, y, hy, hb⟩⟩

omit [IsStrictOrderedRing K] hF in
private theorem definable_boxRadii_section {D : Set (I → K)}
    (hR : A.Definable L {v : Option I → K | v none ∈ boxRadii D (v ∘ some)}) (x : I → K) :
    (Set.univ : Set K).Definable₁ L (boxRadii D x) := by
  let f (v : Fin 1 → K) : Option I → K := fun
    | none => v 0
    | some i => x i
  have hf : (Set.univ : Set K).DefinableMap L f := by
    intro i
    cases i with
    | none => exact (Set.DefinableFun.proj L)
    | some i => exact L.definableFun_const _ (Set.mem_univ (x i))
  exact (hR.mono (Set.subset_univ _)).preimage_map hf

omit [IsStrictOrderedRing K] [Finite I] in
private theorem definable_lowerBounds_boxRadii {D : Set (I → K)}
    (hR : A.Definable L {v : Option I → K | v none ∈ boxRadii D (v ∘ some)}) :
    A.Definable L {v : Option I → K | v none ∈ lowerBounds (boxRadii D (v ∘ some))} := by
  let rename : Option I → Option I ⊕ Unit := fun
    | none => .inr ()
    | some i => .inl (some i)
  have hle : A.Definable L {u : Option I ⊕ Unit → K | u (.inl none) ≤ u (.inr ())} :=
    definable_le_of_definableFunctions F hF (Set.DefinableFun.proj L) (Set.DefinableFun.proj L)
  apply definable_forall_scalar
  convert (hR.preimage_comp rename).compl.union hle using 1
  ext u
  change (u (.inr ()) ∈ boxRadii D ((u ∘ Sum.inl) ∘ some) → u (.inl none) ≤ u (.inr ())) ↔
    ¬ (u ∘ rename) none ∈ boxRadii D ((u ∘ rename) ∘ some) ∨ u (.inl none) ≤ u (.inr ())
  exact imp_iff_not_or

omit [IsStrictOrderedRing K] [Finite I] in
private theorem definable_isGLB_boxRadii {D : Set (I → K)}
    (hR : A.Definable L {v : Option I → K | v none ∈ boxRadii D (v ∘ some)}) :
    A.Definable L {v : Option I → K | IsGLB (boxRadii D (v ∘ some)) (v none)} := by
  have hLower := definable_lowerBounds_boxRadii F hF hR
  let rename : Option I → Option I ⊕ Unit := fun
    | none => .inr ()
    | some i => .inl (some i)
  have hle : A.Definable L {u : Option I ⊕ Unit → K | u (.inr ()) ≤ u (.inl none)} :=
    definable_le_of_definableFunctions F hF (Set.DefinableFun.proj L) (Set.DefinableFun.proj L)
  have hGreatest : A.Definable L {v : Option I → K |
      ∀ r ∈ lowerBounds (boxRadii D (v ∘ some)), r ≤ v none} := by
    apply definable_forall_scalar
    convert (hLower.preimage_comp rename).compl.union hle using 1
    ext u
    change (u (.inr ()) ∈ lowerBounds (boxRadii D ((u ∘ Sum.inl) ∘ some)) →
      u (.inr ()) ≤ u (.inl none)) ↔
      ¬ (u ∘ rename) none ∈ lowerBounds (boxRadii D ((u ∘ rename) ∘ some)) ∨ u (.inr ()) ≤ u (.inl none)
    exact imp_iff_not_or
  exact hLower.inter hGreatest

variable [TopologicalSpace K] [OrderTopology K]

/-- The closure of a definable set is the zero set of a continuous
function definable over the original parameters. -/
theorem exists_continuous_definable_zeroSet_of_closure (hOM : IsOMinimal (K := K) L)
    {D : Set (I → K)} (hD : A.Definable L D) :
    ∃ f : (I → K) → K, A.DefinableFun L f ∧ Continuous f ∧ {x | f x = 0} = closure D := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 1, definable_const_of_closed_term F.one 1 hF.one, continuous_const, by simp⟩
  have hR := definable_boxRadii_relation F hF hD
  choose f hf using fun x => hOM.exists_isGLB (definable_boxRadii_section hR x)
    (boxRadii_nonempty hne x) (boxRadii_bddBelow D x)
  refine ⟨f, ?_, continuous_of_isGLB_boxRadii hf, ?_⟩
  · have he : f.tupleGraph = {v : Option I → K | IsGLB (boxRadii D (v ∘ some)) (v none)} := by
      ext v
      change f (v ∘ some) = v none ↔ IsGLB (boxRadii D (v ∘ some)) (v none)
      exact ⟨fun he => he ▸ hf _, fun ha => (hf _).unique ha⟩
    change A.Definable L f.tupleGraph
    rw [he]
    exact definable_isGLB_boxRadii F hF hR
  · ext x
    exact isGLB_boxRadii_eq_zero_iff_mem_closure (hf x)

/-- A locally closed definable set is the difference of two zero sets
of continuous functions over the same parameters. -/
theorem exists_continuous_definable_description_of_locallyClosed (hOM : IsOMinimal (K := K) L)
    {C : Set (I → K)} (hC : A.Definable L C) (hLC : IsLocallyClosed C) :
    ∃ f g : (I → K) → K, A.DefinableFun L f ∧ A.DefinableFun L g ∧
      Continuous f ∧ Continuous g ∧ C = {x | f x = 0 ∧ g x ≠ 0} := by
  obtain ⟨f, hf, hfc, hfZ⟩ := exists_continuous_definable_zeroSet_of_closure F hF hOM hC
  have hz : A.DefinableFun L (fun _ : I → K => (0 : K)) :=
    definable_const_of_closed_term F.zero 0 hF.zero
  have hClose : A.Definable L (closure C) := hfZ ▸ hf.ofPred_eq hz
  have hBoundary : IsClosed (closure C \ C) := isOpen_compl_iff.mp hLC.isOpen_coborder
  obtain ⟨g, hg, hgc, hgZ⟩ := exists_continuous_definable_zeroSet_of_closure F hF hOM (hClose.sdiff hC)
  rw [hBoundary.closure_eq] at hgZ
  refine ⟨f, g, hf, hg, hfc, hgc, ?_⟩
  ext x
  have hfx : f x = 0 ↔ x ∈ closure C := Set.ext_iff.mp hfZ x
  have hgx : g x = 0 ↔ x ∈ closure C \ C := Set.ext_iff.mp hgZ x
  change x ∈ C ↔ f x = 0 ∧ ¬g x = 0
  rw [hfx, not_congr hgx]
  exact ⟨fun hx => ⟨subset_closure hx, fun hb => hb.2 hx⟩,
    fun h => not_not.mp (fun hn => h.2 ⟨h.1, hn⟩)⟩

/-- Continuous-function description in Remark 2.3, given the finite
definable cell decomposition. Every piece contributes two continuous
functions definable over the same base. -/
theorem exists_continuous_definable_description_of_cell_decomposition
    (hOM : IsOMinimal (K := K) L) {D : Set (I → K)} {m : ℕ}
    (cells : Fin m → Set (I → K)) (hCells : ∀ i, A.Definable L (cells i) ∧ IsLocallyClosed (cells i))
    (hD : D = ⋃ i, cells i) :
    ∃ f g : Fin m → (I → K) → K,
      (∀ i, A.DefinableFun L (f i) ∧ A.DefinableFun L (g i) ∧ Continuous (f i) ∧ Continuous (g i)) ∧
      D = ⋃ i, {x | f i x = 0 ∧ g i x ≠ 0} := by
  choose f g hf hg hfc hgc he using fun i =>
    exists_continuous_definable_description_of_locallyClosed F hF hOM (hCells i).1 (hCells i).2
  exact ⟨f, g, fun i => ⟨hf i, hg i, hfc i, hgc i⟩, by rw [hD]; simp only [he]⟩

end Definability

section UniversalAxiomatization

variable {J : Language.{u, v}} [J.Structure K] [TopologicalSpace K] [OrderTopology K]

private theorem exists_point_avoiding_finite_inverse_terms
    (hContinuous : ∀ {n} (f : J.Functions n), Continuous (Structure.funMap f : (Fin n → K) → K))
    (F : Finset (J.Term Unit)) :
    ∃ x : K, ∀ t ∈ F, t.realize (fun _ => x) ≠ x⁻¹ := by
  have hTerm (t : J.Term Unit) : Continuous (fun x : K => t.realize (fun _ => x)) := by
    induction t with
    | var _ => exact continuous_id
    | func f _ ih => exact (hContinuous f).comp (continuous_pi ih)
  let : (𝓝[>] (0 : K)).NeBot := nhdsGT_neBot_of_exists_gt ⟨1, zero_lt_one⟩
  apply Filter.Eventually.exists (f := 𝓝[>] (0 : K))
  apply (Filter.eventually_all_finite F.finite_toSet).mpr
  intro t _
  let c : K := t.realize (fun _ => 0) + 1
  have hb : ∀ᶠ x in 𝓝[>] (0 : K), t.realize (fun _ => x) < c :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((hTerm t).continuousAt.eventually_lt continuousAt_const (lt_add_one _))
  have hi : ∀ᶠ x in 𝓝[>] (0 : K), c < x⁻¹ := tendsto_inv_nhdsGT_zero.eventually_gt_atTop c
  exact (hb.and hi).mono fun _ h => (h.1.trans h.2).ne

private def graphAtTerm (φ : J.Formula (Unit ⊕ Unit)) (t : J.Term Unit) : J.Formula Unit :=
  φ.subst (Sum.elim Term.var (fun _ => t))

private theorem realize_graphAtTerm {M : Type*} [J.Structure M]
    (φ : J.Formula (Unit ⊕ Unit)) (t : J.Term Unit) (x : Unit → M) :
    (graphAtTerm φ t).Realize x ↔ φ.Realize (Sum.elim x (fun _ => t.realize x)) := by
  unfold graphAtTerm Formula.Realize
  rw [BoundedFormula.realize_subst]
  have he : (fun i : Unit ⊕ Unit => (Sum.elim Term.var (fun _ => t) i).realize x) =
      Sum.elim x (fun _ => t.realize x) := by
    funext i
    cases i <;> rfl
  rw [he]

/-- The continuous functional language in Remark 2.3 cannot give a
universal theory with quantifier elimination. The inverse graph only
needs to be provably total and single-valued in the theory. -/
theorem not_isUniversal_of_continuous_functions_and_inverse
    (T : J.Theory) [K ⊨ T] (hQE : EliminatesQuantifiers T)
    (hContinuous : ∀ {n} (f : J.Functions n), Continuous (Structure.funMap f : (Fin n → K) → K))
    (φ : J.Formula (Unit ⊕ Unit))
    (hInv : ∀ x y : K, φ.Realize (Sum.elim (fun _ => x) (fun _ => y)) ↔ y = x⁻¹)
    (hTotal : ∀ (M : Type (max u v)), ∀ [J.Structure M] [M ⊨ T],
      ∀ x : Unit → M, ∃ y : M, ∀ z, φ.Realize (Sum.elim x (fun _ => z)) ↔ z = y) :
    ¬ T.IsUniversal := by
  classical
  intro hU
  let := hU
  let l := J.lhomWithConstants Unit
  let avoid (t : J.Term Unit) : J[[Unit]].Sentence := Formula.equivSentence (graphAtTerm φ t).not
  let D : J[[Unit]].Theory := l.onTheory T ∪ Set.range avoid
  have hSat : D.IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro U hU
    let V := U.filter (fun σ => σ ∉ l.onTheory T)
    have hV : (V : Set _) ⊆ avoid '' (Set.univ : Set (J.Term Unit)) := by
      intro σ hσ
      obtain ⟨hUσ, hbase⟩ := Finset.mem_filter.mp hσ
      rw [Set.image_univ]
      exact (hU hUσ).resolve_left hbase
    obtain ⟨F, _, hF⟩ := Finset.subset_set_image_iff.mp hV
    obtain ⟨x, hx⟩ := exists_point_avoiding_finite_inverse_terms hContinuous F
    let : (constantsOn Unit).Structure K := constantsOn.structure (fun _ => x)
    have hBase : K ⊨ l.onTheory T := (LHom.onTheory_model l T).mpr inferInstance
    have hModel : K ⊨ (U : J[[Unit]].Theory) := by
      constructor
      intro σ hσ
      by_cases hT : σ ∈ l.onTheory T
      · exact hBase.realize_of_mem _ hT
      have hσ' : σ ∈ F.image avoid := hF.symm ▸ Finset.mem_filter.mpr ⟨hσ, hT⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hσ'
      apply (Formula.realize_equivSentence K _).mpr
      rw [Formula.realize_not, realize_graphAtTerm]
      exact fun he => hx t ht ((hInv _ _).mp he)
    exact Theory.Model.isSatisfiable K
  let A := hSat.some
  let := l.reduct A
  have hA : A ⊨ T :=
    (LHom.onTheory_model l _).mp (Theory.Model.mono A.is_model Set.subset_union_left)
  let := hA
  let x (i : Unit) : A := ↑(J.con i)
  obtain ⟨y, hy⟩ := hTotal A x
  obtain ⟨t, ht⟩ := exists_term_of_uniquely_definable hQE x y φ hy
  have hAvoid := (Formula.realize_equivSentence A (graphAtTerm φ t).not).mp
    (A.is_model.realize_of_mem (avoid t) (Or.inr ⟨t, rfl⟩))
  rw [Formula.realize_not, realize_graphAtTerm] at hAvoid
  exact hAvoid ((hy _).mpr ht)

end UniversalAxiomatization

section FunctionalLanguage

variable {L : Language.{u, v}} [L.Structure K] [TopologicalSpace K]

/-- A function symbol for each parameter-free definable total
continuous function on a finite Cartesian power. -/
abbrev ContinuousDefinableFunctions (L : Language.{u, v}) (K : Type*)
    [L.Structure K] [TopologicalSpace K] (n : ℕ) :=
  {f : (Fin n → K) → K // (∅ : Set K).DefinableFun L f ∧ Continuous f}

/-- The continuous functional presentation of the given ordered model. -/
abbrev ContinuousFunctionalLanguage :=
  OrderedFunctionalLanguage (ContinuousDefinableFunctions L K)

@[expose, instance_reducible]
def continuousFunctionalStructure :
    (ContinuousFunctionalLanguage (L := L) (K := K)).Structure K where
  funMap f := f.val
  RelMap r x := match r with | .le => x 0 ≤ x 1

variable [OrderTopology K]

set_option linter.style.haveILetI false in
/-- A cell decomposition over the empty base gives a quantifier-free
description in the language of all parameter-free continuous functions.
In particular, the original function graphs and relations can be
defined in that language. -/
theorem exists_formula_continuousFunctionalLanguage
    (F : OrderedFieldTerms L) (hF : InterpretsOrderedFieldTerms F (A := K))
    (hOM : IsOMinimal (K := K) L) {m n : ℕ} (D : Set (Fin n → K))
    (cells : Fin m → Set (Fin n → K))
    (hCells : ∀ i, (∅ : Set K).Definable L (cells i) ∧ IsLocallyClosed (cells i))
    (hD : D = ⋃ i, cells i) :
    letI := continuousFunctionalStructure (L := L) (K := K)
    ∃ φ : (ContinuousFunctionalLanguage (L := L) (K := K)).Formula (Fin n),
      φ.IsQF ∧ ∀ x, x ∈ D ↔ φ.Realize x := by
  classical
  let J := ContinuousFunctionalLanguage (L := L) (K := K)
  letI := continuousFunctionalStructure (L := L) (K := K)
  obtain ⟨f, g, h, he⟩ :=
    exists_continuous_definable_description_of_cell_decomposition F hF hOM cells hCells hD
  let zero : J.Functions 0 :=
    ⟨fun _ => 0, definable_const_of_closed_term F.zero 0 hF.zero, continuous_const⟩
  let zeroTerm : J.Term (Fin n) := .func zero Fin.elim0
  let clauses (i : Fin m) : J.Formula (Fin n) :=
    ((Term.func (⟨f i, (h i).1, (h i).2.2.1⟩ : J.Functions n) Term.var).equal zeroTerm) ⊓
      ((Term.func (⟨g i, (h i).2.1, (h i).2.2.2⟩ : J.Functions n) Term.var).equal zeroTerm).not
  refine ⟨Formula.iSup clauses, ?_, ?_⟩
  · have hq (i : Fin m) : (clauses i).IsQF := by
      exact BoundedFormula.IsQF.inf (.of_isAtomic (.equal _ _))
        (.not (.of_isAtomic (.equal _ _)))
    have foldQF (l : List (Fin m)) : ((l.map clauses).foldr (· ⊔ ·) ⊥).IsQF := by
      induction l with
      | nil => exact BoundedFormula.isQF_bot
      | cons i l ih => exact (hq i).sup ih
    unfold Formula.iSup BoundedFormula.iSup
    exact foldQF _
  · intro x
    rw [he, Set.mem_iUnion, Formula.realize_iSup]
    apply exists_congr
    intro i
    simp only [clauses, Formula.realize_inf, Formula.realize_not, Formula.realize_equal,
      Term.realize_func, Term.realize_var, zeroTerm]
    change (f i x = 0 ∧ g i x ≠ 0) ↔
      f i (fun j => x j) = 0 ∧ ¬g i (fun j => x j) = 0
    rfl

end FunctionalLanguage

end GeneralizedEuler.Section2
