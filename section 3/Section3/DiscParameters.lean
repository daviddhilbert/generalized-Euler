module

public import Section3.DefinablePoints
public import Mathlib.Order.Interval.Set.IsoIoo

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Cardinal Set
universe u v
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO in
/-- Every disc of finite additive radius has the cardinality of the
field. Scale a copy of the interval (-1,1) into its open subdisc. -/
theorem card_openDisc [DenselyOrdered O.ValueGroup] (a : K) {r : O.ValueGroup} (hr : r ≠ 0) :
    #(openDisc O a r) = #K := by
  obtain ⟨s,hs,hsr⟩ := exists_between (pos_iff_ne_zero.mpr hr)
  obtain ⟨d,hd⟩ := O.valuation_surjective s
  have hdn : d ≠ 0 := (map_ne_zero O.valuation).mp (hd.trans_ne hs.ne')
  let u := orderIsoIooNegOneOne K
  let embed (x : K) : openDisc O a r := ⟨d * (u x).val + a, by
    change O.valuation (d * _ + a - a) < r
    rw [add_sub_cancel_right,map_mul,hd]
    have h := valuation_le_of_abs_le_abs O hO
      (show |(u x).val| ≤ |(1 : K)| by simpa using (abs_lt.mpr (u x).property).le)
    exact (mul_le_of_le_one_right (zero_le : 0 ≤ s) (by simpa using h)).trans_lt hsr⟩
  apply (mk_set_le _).antisymm
  apply mk_le_of_injective (f := embed)
  intro x y h
  apply u.injective
  exact Subtype.ext (mul_left_cancel₀ hdn (add_right_cancel (congrArg Subtype.val h)))

include hO in
theorem card_finite_radius_disc [DenselyOrdered O.ValueGroup] (a : K)
    {r : O.ValueGroup} (hr : r ≠ 0) (closed : Bool) :
    #((if closed then closedDisc else openDisc) O a r) = #K := by
  cases closed
  · exact card_openDisc O hO a hr
  · apply (mk_set_le _).antisymm
    rw [←card_openDisc O hO a hr]
    exact mk_le_mk_of_subset (fun x hx => (show O.valuation (x-a) < r from hx).le)

section
variable {L : Language.{u,v}} [L.Structure K]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- Eliminate all the centers simultaneously. Their radii may already
be among the arbitrary RV parameters eliminated by 3.6. -/
theorem field_closure_of_all_center_choices
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hK : μ < #K) (hL : #(Σ i, L.Functions i) ≤ μ)
    (exchange : ∀ (B : Set K) (a c : K), a ∈ Substructure.closure L (insert c B) →
      a ∉ Substructure.closure L B → c ∈ Substructure.closure L (insert a B))
    {n : ℕ} (D : Fin n → Set K) (hD : ∀ i, #(D i) = #K) (B : Set K) (hB : #B ≤ μ)
    (a : K) (hrep : ∀ c : Fin n → K, (∀ i, c i ∈ D i) →
      a ∈ Substructure.closure L (B ∪ range c)) : a ∈ Substructure.closure L B := by
  classical
  induction n generalizing B with
  | zero => simpa using hrep Fin.elim0 (fun i => i.elim0)
  | succ n ih =>
    have size (v : K) : #(insert v B : Set K) ≤ μ :=
      Cardinal.mk_insert_le.trans (Cardinal.add_le_of_le hμ hB (one_le_aleph0.trans hμ))
    have one (c : K) (hc : c ∈ D 0) : a ∈ Substructure.closure L (insert c B) := by
      apply ih (fun j => D j.succ) (fun j => hD j.succ) _ (size c)
      intro rest hrest
      have H := hrep (Fin.cons c rest) (Fin.cases hc hrest)
      simpa only [Fin.range_cons,union_insert,insert_union] using H
    by_contra ha
    have hsub : D 0 ⊆ (Substructure.closure L (insert a B) : Set K) :=
      fun c hc => exchange B a c (one c hc) ha
    have hle := (mk_le_mk_of_subset hsub).trans (card_fieldClosure_le hμ hL _ (size a))
    exact hK.not_ge ((hD 0) ▸ hle)
end

section
variable {L : Language.{u,v}} {E : Type*} [L.Structure K] [L.Structure (Residue O)]
  (powers : E → RV0 O → RV0 O)
local notation "M" => canonicalStructure (L := L) O hO powers

/-- Representatives for a tuple of named disc imaginaries: a field center
and an RV representative of its radius. Open/closed tags are fixed. -/
def representsDiscTuple {n : ℕ} (closed : Fin n → Bool) (D : Fin n → DiscCode O)
    (centers : Fin n → K) (tags : Fin n → RV0 O) : Prop :=
  ∀ i, (D i).points O = (if closed i then closedDisc else openDisc) O
    (centers i) (unsignedValue O (tags i))

abbrev discAssignment {n : ℕ} (c : Fin n → K) (t : Fin n → RV0 O) :
    ∀ s, Fin n → CanonicalSort O s
  | .vf => c
  | .rv => t

/-- Definability over the ordinary base plus the named disc codes, by
pullback to the quotient presentation. The same formula works for every
choice of representatives of those codes. -/
def definableWithDiscParameters {n : ℕ} (P : ∀ s, Set (CanonicalSort O s))
    (closed : Fin n → Bool) (D : Fin n → DiscCode O) {V : TCsort → Type*}
    (A : Set (∀ s, V s → CanonicalSort O s)) : Prop :=
  ∃ φ : SortedFormula L E (fun s => (P s : Type u) ⊕ (Fin n ⊕ V s)),
    ∀ c t, representsDiscTuple O closed D c t → ∀ x,
      x ∈ A ↔ φ.realize M (fun s => Sum.elim Subtype.val (Sum.elim (discAssignment O c t s) (x s)))

theorem definableWithDiscParameters.withRepresentatives {n : ℕ}
    {P : ∀ s, Set (CanonicalSort O s)} {closed : Fin n → Bool} {D : Fin n → DiscCode O}
    {V : TCsort → Type*} {A : Set (∀ s, V s → CanonicalSort O s)}
    (h : definableWithDiscParameters (L := L) O hO powers P closed D A)
    {c : Fin n → K} {t : Fin n → RV0 O} (ht : representsDiscTuple O closed D c t) :
    SortedDefinableOver M (fun s => P s ∪ range (discAssignment O c t s)) A := by
  obtain ⟨φ,hφ⟩ := h
  let S (s) := P s ∪ range (discAssignment O c t s)
  let rename (s) : P s ⊕ (Fin n ⊕ V s) → (S s : Type u) ⊕ V s
    | .inl a => .inl ⟨a.val,Or.inl a.property⟩
    | .inr (.inl i) => .inl ⟨_,Or.inr (mem_range_self i)⟩
    | .inr (.inr i) => .inr i
  refine ⟨φ.relabel rename,fun x => (hφ c t ht x).trans ?_⟩
  rw [φ.realize_relabel]
  apply Iff.of_eq
  apply congrArg (φ.realize M)
  funext s i
  rcases i with a | i | j <;> rfl

/-- Lemma 3.8: a finite tuple of finite-radius disc codes adds no new
field point over a small, field-closed base. Section 2's small immediate
automorphisms eliminate the arbitrary RV representatives before exchange. -/
theorem field_point_over_disc_parameters {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hK : μ < #K)
    (hL : #(Σ i, L.Functions i) ≤ μ) [DenselyOrdered O.ValueGroup]
    (exchange : ∀ (B : Set K) (a c : K), a ∈ Substructure.closure L (insert c B) →
      a ∉ Substructure.closure L B → c ∈ Substructure.closure L (insert a B))
    (move : ∀ (S : SortedSubstructure M), #(S.carrier .vf) ≤ μ →
      ∀ a ∉ S.carrier .vf, ∃ e : SortedIsomorphism M M, e.toEmbedding .vf a ≠ a ∧
        (∀ x ∈ S.carrier .vf, e.toEmbedding .vf x = x) ∧ ∀ t, e.toEmbedding .rv t = t)
    (P : ∀ s, Set (CanonicalSort O s)) (hP : #(P .vf) ≤ μ)
    {n : ℕ} (closed : Fin n → Bool) (D : Fin n → DiscCode O)
    (old : Fin n → K) (t : Fin n → RV0 O) (hr : ∀ i, unsignedValue O (t i) ≠ 0)
    (hrep : representsDiscTuple O closed D old t)
    {V : TCsort → Type*} (x : ∀ s, V s → CanonicalSort O s)
    (hx : definableWithDiscParameters (L := L) O hO powers P closed D {x}) :
    range (x .vf) ⊆ (Substructure.closure L (P .vf) : Set K) := by
  rintro _ ⟨j,rfl⟩
  have size (i) : #((D i).points O) = #K := by
    rw [hrep i]; exact card_finite_radius_disc O hO _ (hr i) _
  apply field_closure_of_all_center_choices hμ hK hL exchange _ size _ hP
  intro c hc
  have rep : representsDiscTuple O closed D c t := by
    intro i
    have hi := hc i
    rw [hrep i] at hi ⊢
    cases he : closed i <;> simp only [he,Bool.false_eq_true,ite_false,ite_true] at hi ⊢
    · exact (openDisc_change_center O hi).symm
    · exact (closedDisc_change_center O hi).symm
  have hsize : #(P .vf ∪ range c : Set K) ≤ μ :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hμ hP
      ((Cardinal.mk_lt_aleph0_iff.mpr (inferInstance : Finite (range c))).le.trans hμ))
  exact vf_range_subset_fieldClosure_of_small_immediate_movers O hO powers hμ hL move
    _ hsize (hx.withRepresentatives O hO powers rep) (mem_range_self j)

/-- The second assertion of 3.15 at the level of types. A formula over
the named discs can use the input tuple itself as its choice of centers.
An immediate automorphism need only move that tuple and fix the RV sort.
The RV part of the parameter base may be the entire RV sort. -/
theorem polydisc_uniform_over_its_codes {n : ℕ} (P : ∀ s, Set (CanonicalSort O s))
    (D : Fin n → DiscCode O) (c : Fin n → K) (t : Fin n → RV0 O)
    (hrep : representsDiscTuple O (fun _ => false) D c t)
    {V : TCsort → Type*} (coords : V .vf ≃ Fin n) [IsEmpty (V .rv)]
    {A : Set (∀ s, V s → CanonicalSort O s)}
    (hA : definableWithDiscParameters (L := L) O hO powers P (fun _ => false) D A)
    (move : ∀ x y : Fin n → K, (∀ i, x i ∈ (D i).points O) → (∀ i, y i ∈ (D i).points O) →
      ∃ e : SortedIsomorphism M M, (∀ i, e.toEmbedding .vf (x i) = y i) ∧
        (∀ a ∈ P .vf, e.toEmbedding .vf a = a) ∧ ∀ u, e.toEmbedding .rv u = u)
    (x y : ∀ s, V s → CanonicalSort O s)
    (hx : ∀ i, x .vf (coords.symm i) ∈ (D i).points O)
    (hy : ∀ i, y .vf (coords.symm i) ∈ (D i).points O) : x ∈ A ↔ y ∈ A := by
  obtain ⟨φ,hφ⟩ := hA
  let centers (z : ∀ s, V s → CanonicalSort O s) (i : Fin n) := z .vf (coords.symm i)
  have rep (z : ∀ s, V s → CanonicalSort O s) (hz : ∀ i, centers z i ∈ (D i).points O) :
      representsDiscTuple O (fun _ => false) D (centers z) t := by
    intro i
    have hi := hz i
    rw [hrep i] at hi ⊢
    exact (openDisc_change_center O hi).symm
  obtain ⟨e,hxy,hfix,hRV⟩ := move (centers x) (centers y) hx hy
  let vals (z : ∀ s, V s → CanonicalSort O s) (s : TCsort) :=
    Sum.elim (Subtype.val (p := (· ∈ P s))) (Sum.elim (discAssignment O (centers z) t s) (z s))
  have hmap : e.toSortedEmbedding.mapAssignment (vals x) = vals y := by
    funext s i
    rw [SortedEmbedding.mapAssignment_apply]
    rcases i with a | i | j
    · cases s with
      | vf => exact hfix _ a.property
      | rv => exact hRV _
    · cases s with
      | vf => exact hxy i
      | rv => exact hRV _
    · cases s with
      | vf => simpa [centers,vals] using hxy (coords j)
      | rv => exact isEmptyElim j
  have he := e.realize_iff φ (vals x)
  rw [hmap] at he
  exact (hφ _ _ (rep x hx) x).trans (he.symm.trans (hφ _ _ (rep y hy) y).symm)

end

end GeneralizedEuler.Section3
