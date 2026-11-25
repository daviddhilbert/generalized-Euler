module

public import Mathlib.Order.Interval.Set.OrdConnectedComponent
public import Mathlib.Order.Preorder.Finite
public import Section2.ValuativeInterval

/-! Uniqueness of the interval pieces in Holly normal form. -/

public section

namespace GeneralizedEuler.Section2

private theorem ordConnected_union_of_bridge {A : Type*} [LinearOrder A]
    {D B : Set A} (hD : Set.OrdConnected D) (hB : Set.OrdConnected B)
    {x y : A} (hx : x ∈ D) (hy : y ∈ B) (hxy : Set.uIcc x y ⊆ D ∪ B) :
    Set.OrdConnected (D ∪ B) := by
  apply Set.ordConnected_of_uIcc_subset_left (x := x)
  intro z hz
  rcases hz with hz | hz
  · exact (hD.uIcc_subset hx hz).trans Set.subset_union_left
  · exact Set.uIcc_subset_uIcc_union_uIcc.trans
      (Set.union_subset hxy ((hB.uIcc_subset hy hz).trans Set.subset_union_right))

private theorem finite_piece_eq_ordConnectedComponent {A : Type*} [LinearOrder A]
    {U D : Set A} (pieces : Finset (Set A))
    (hne : ∀ B ∈ pieces, B.Nonempty) (hconv : ∀ B ∈ pieces, Set.OrdConnected B)
    (hcover : U = ⋃ B ∈ pieces, B)
    (hgap : ∀ B ∈ pieces, ∀ C ∈ pieces, B ≠ C → ¬ Set.OrdConnected (B ∪ C))
    (hD : D ∈ pieces) {x : A} (hx : x ∈ D) :
    D = Set.ordConnectedComponent U x := by
  classical
  let component := Set.ordConnectedComponent U x
  have cover (y : A) : y ∈ U ↔ ∃ B ∈ pieces, y ∈ B := by
    rw [hcover]
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨B, hB, hy⟩ => ⟨B, hB, hy⟩, fun ⟨B, hB, hy⟩ => ⟨B, hB, hy⟩⟩
  have hsub {B : Set A} (hB : B ∈ pieces) : B ⊆ U :=
    fun y hy => (cover y).mpr ⟨B, hB, hy⟩
  have separated {B C : Set A} (hB : B ∈ pieces) (hC : C ∈ pieces) (hBC : B ≠ C)
      {z : A} (hzB : z ∈ B) (hzC : z ∈ C) : False := by
    apply hgap B hB C hC hBC
    exact ordConnected_union_of_bridge (hconv B hB) (hconv C hC) hzB hzC
      (by rw [Set.uIcc_self]; exact Set.singleton_subset_iff.mpr (Or.inl hzB))
  have inComponent {B : Set A} (hB : B ∈ pieces) {z : A}
      (hz : z ∈ component) (hzB : z ∈ B) : B ⊆ component := by
    intro w hw
    exact Set.mem_ordConnectedComponent_trans hz
      ((hconv B hB).uIcc_subset hzB hw |>.trans (hsub hB))
  have hforward : D ⊆ component := by
    let := hconv D hD
    exact Set.subset_ordConnectedComponent hx (hsub hD)
  apply hforward.antisymm
  intro y hy
  by_contra hyD
  obtain ⟨E, hE, hyE⟩ := (cover y).mp (Set.ordConnectedComponent_subset hy)
  let candidates := pieces.filter (fun B => B ≠ D ∧ B ⊆ component)
  have hCandidates : candidates.Nonempty :=
    ⟨E, Finset.mem_filter.mpr ⟨hE, fun h => hyD (h ▸ hyE), inComponent hE hy hyE⟩⟩
  let point (B : Set A) : A := if hB : B ∈ pieces then (hne B hB).some else x
  have point_mem (B : Set A) (hB : B ∈ pieces) : point B ∈ B := by
    simp only [point, dite_eq_left hB, Set.Nonempty.some_mem]
  obtain ⟨B, hmin⟩ := candidates.exists_minimalFor (fun B => Set.uIcc x (point B)) hCandidates
  obtain ⟨hB, hBD, hBsub⟩ := Finset.mem_filter.mp hmin.1
  have hbridge := Set.mem_ordConnectedComponent.mp (hBsub (point_mem B hB))
  have hnot : ¬ Set.uIcc x (point B) ⊆ D ∪ B :=
    fun h => hgap D hD B hB hBD.symm
      (ordConnected_union_of_bridge (hconv D hD) (hconv B hB) hx (point_mem B hB) h)
  obtain ⟨z, hz, hzNot⟩ := Set.not_subset.mp hnot
  obtain ⟨C, hC, hzC⟩ := (cover z).mp (hbridge hz)
  have hCD : C ≠ D := fun h => hzNot (Or.inl (h ▸ hzC))
  have hCB : C ≠ B := fun h => hzNot (Or.inr (h ▸ hzC))
  have hCsub := inComponent hC
    (Set.mem_ordConnectedComponent.mpr ((Set.uIcc_subset_uIcc_left hz).trans hbridge)) hzC
  have hCandC : C ∈ candidates := Finset.mem_filter.mpr ⟨hC, hCD, hCsub⟩
  have hxC : x ∉ C := fun h => separated hD hC hCD.symm hx h
  have hbC : point B ∉ C := fun h => separated hB hC hCB.symm (point_mem B hB) h
  have hcBetween : point C ∈ Set.uIcc x (point B) := by
    change min x (point B) ≤ point C ∧ point C ≤ max x (point B)
    have hlo : min x (point B) ∉ C := min_rec' (· ∉ C) hxC hbC
    have hhi : max x (point B) ∉ C := max_rec' (· ∉ C) hxC hbC
    refine ⟨?_, ?_⟩
    · by_contra! h
      exact hlo ((hconv C hC).out (point_mem C hC) hzC ⟨h.le, hz.1⟩)
    · by_contra! h
      exact hhi ((hconv C hC).out hzC (point_mem C hC) ⟨hz.2, h.le⟩)
  have hshort := Set.uIcc_subset_uIcc_left hcBetween
  have hlong : Set.uIcc x (point B) ⊆ Set.uIcc x (point C) := hmin.2 hCandC hshort
  have hEq := (Set.uIcc_injective_left x) (hlong.antisymm hshort)
  exact hbC (hEq.symm ▸ point_mem C hC)

variable {K : Type*} [Field K] [LinearOrder K] (O : ValuationSubring K)

theorem IsHollyDecomposition.piece_eq_component {U : Set K} {pieces : Finset (Set K)}
    (h : IsHollyDecomposition O U pieces) {D : Set K} (hD : D ∈ pieces)
    {x : K} (hx : x ∈ D) : D = Set.ordConnectedComponent U x := by
  have hconn (B : Set K) (hB : B ∈ pieces) : Set.OrdConnected B := by
    obtain ⟨_, lo, hi, _, _, rfl⟩ := h.1 B hB
    exact valuativeInterval_ordConnected lo hi
  exact finite_piece_eq_ordConnectedComponent pieces (fun B hB => (h.1 B hB).1) hconn h.2.1
    (fun B hB C hC hne hBC => h.2.2 B hB C hC hne
      (IsValuativeInterval.union_of_ordConnected O (h.1 B hB) (h.1 C hC) hBC)) hD hx

/-- The interval pieces of a Holly decomposition are exactly the order
components of the set. Thus the finite set of pieces is unique. -/
theorem hollyDecomposition_unique {U : Set K} {pieces pieces' : Finset (Set K)}
    (h : IsHollyDecomposition O U pieces) (h' : IsHollyDecomposition O U pieces') :
    pieces = pieces' := by
  have incl {P Q : Finset (Set K)} (hP : IsHollyDecomposition O U P)
      (hQ : IsHollyDecomposition O U Q) : P ⊆ Q := by
    intro D hD
    obtain ⟨x, hx⟩ := (hP.1 D hD).1
    have hxU : x ∈ U := by
      rw [hP.2.1, Set.mem_iUnion]
      exact ⟨D, Set.mem_iUnion.mpr ⟨hD, hx⟩⟩
    rw [hQ.2.1, Set.mem_iUnion] at hxU
    obtain ⟨B, hm⟩ := hxU
    obtain ⟨hB, hxB⟩ := Set.mem_iUnion.mp hm
    rw [IsHollyDecomposition.piece_eq_component O hP hD hx,
      ← IsHollyDecomposition.piece_eq_component O hQ hB hxB]
    exact hB
  exact (incl h h').antisymm (incl h' h)

private theorem valuativeUnion_of_convex_end {D : Set K} (hd : IsEndDisc O D)
    (hc : Set.OrdConnected D) : ValuativeUnion O D := by
  let e : ValuativeIntervalEnd (K := K) := ⟨D, true⟩
  have he : ∀ v ∈ some e, IsEndDisc O v.disc := by
    intro v hv
    have hv' := Option.some.inj (Option.mem_def.mp hv)
    subst v
    exact hd
  have heq : D = valuativeInterval (some e) (some e) := by
    ext x
    change x ∈ D ↔ (∃ d ∈ D, d ≤ x) ∧ ∃ d ∈ D, x ≤ d
    constructor
    · exact fun h => ⟨⟨x, h, le_rfl⟩, x, h, le_rfl⟩
    · rintro ⟨⟨a, ha, hax⟩, b, hb, hxb⟩
      exact hc.out ha hb ⟨hax, hxb⟩
  rw [heq]
  exact ValuativeUnion.of_ends _ _ he he

section UnarySets

variable [IsStrictOrderedRing K]

private theorem openDisc_valuativeUnion (hO : IsOrderConvex O) (a : K) (r : O.ValueGroup) :
    ValuativeUnion O (openDisc O a r) := by
  by_cases hr : r = 0
  · have h : openDisc O a r = ∅ := by
      ext x
      simp [openDisc, hr]
    rw [h]
    exact .empty
  · apply valuativeUnion_of_convex_end O (.inr ⟨a, r, hr, Or.inl rfl⟩)
    exact valuativeDisc_ordConnected O hO a (Set.Iio r)
      (fun {_ _} hxy hy => hxy.trans_lt hy)

private theorem closedDisc_valuativeUnion (hO : IsOrderConvex O) (a : K) (r : O.ValueGroup) :
    ValuativeUnion O (closedDisc O a r) := by
  by_cases hr : r = 0
  · have h : closedDisc O a r = {a} := by
      ext x
      simp [closedDisc, hr, nonpos_iff_eq_zero, sub_eq_zero]
    rw [h]
    exact valuativeUnion_of_convex_end O (.inl ⟨a, rfl⟩) Set.ordConnected_singleton
  · apply valuativeUnion_of_convex_end O (.inr ⟨a, r, hr, Or.inr rfl⟩)
    exact valuativeDisc_ordConnected O hO a (Set.Iic r)
      (fun {_ _} hxy hy => hxy.trans hy)

/-- The Boolean description of a unary VF set by order and valuation
conditions, as used with van den Dries (1997), Proposition 7.6. -/
inductive UnaryValuativeSet : Set K → Prop where
  | point (a : K) : UnaryValuativeSet {a}
  | orderBelow (a : K) : UnaryValuativeSet (Set.Iio a)
  | valueEq (a : K) (r : O.ValueGroup) : UnaryValuativeSet {x | O.valuation (x - a) = r}
  | valueLT (a : K) (r : O.ValueGroup) : UnaryValuativeSet (openDisc O a r)
  | union {U V} : UnaryValuativeSet U → UnaryValuativeSet V → UnaryValuativeSet (U ∪ V)
  | inter {U V} : UnaryValuativeSet U → UnaryValuativeSet V → UnaryValuativeSet (U ∩ V)
  | compl {U} : UnaryValuativeSet U → UnaryValuativeSet Uᶜ

theorem UnaryValuativeSet.valuativeUnion (hO : IsOrderConvex O)
    {U : Set K} (h : UnaryValuativeSet O U) : ValuativeUnion O U := by
  induction h with
  | point a =>
    exact valuativeUnion_of_convex_end O (.inl ⟨a, rfl⟩) Set.ordConnected_singleton
  | orderBelow a =>
    have h : valuativeInterval none (some ⟨{a}, false⟩) = Set.Iio a := by
      ext x
      simp [valuativeInterval, allowedAbove, allowedBelow]
    rw [← h]
    apply ValuativeUnion.of_ends
    · simp
    · intro e he
      have he' := Option.some.inj (Option.mem_def.mp he)
      subst e
      exact .inl ⟨a, rfl⟩
  | valueEq a r =>
    have h : {x : K | O.valuation (x - a) = r} =
        closedDisc O a r ∩ (openDisc O a r)ᶜ := by
      ext x
      change _ ↔ O.valuation (x - a) ≤ r ∧ ¬O.valuation (x - a) < r
      rw [not_lt]
      exact le_antisymm_iff
    rw [h]
    exact (closedDisc_valuativeUnion O hO a r).inter (openDisc_valuativeUnion O hO a r).compl
  | valueLT a r => exact openDisc_valuativeUnion O hO a r
  | union _ _ ihU ihV => exact ihU.union ihV
  | inter _ _ ihU ihV => exact ihU.inter ihV
  | compl _ ih => exact ih.compl

/-- The interval components are uniquely determined by a unary Boolean
description of the form used in §2.4. -/
theorem existsUnique_hollyDecomposition (hO : IsOrderConvex O) {U : Set K}
    (h : UnaryValuativeSet O U) : ∃! p : Finset (Set K), IsHollyDecomposition O U p := by
  obtain ⟨p, hp⟩ := (UnaryValuativeSet.valuativeUnion O hO h).exists_hollyDecomposition
  exact ⟨p, hp, fun q hq => hollyDecomposition_unique O hq hp⟩

end UnarySets

end GeneralizedEuler.Section2
