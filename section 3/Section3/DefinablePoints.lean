module

public import Section2.FieldClosureUnderRV
public import Section2.RVClosure
public import Section2.DiscCodes
public import Section2.DefinableHolly

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder

universe u v w z
variable {L : Language.{u,v}} {E : Type w} {Z : TCsort → Type z}
  (M : SortedStructure L E Z) (S : SortedSubstructure M)

/-- The RV assertion of 3.19, with the Section 2 QE and RV closure inputs.
The formula starts over both sorts of S. -/
theorem rv_definable_point_mem
    (hRV : RVDefinablyClosed M (S.carrier .rv))
    (hQE : ∀ φ : SortedFormula L E (FullRVVariables S Unit),
      ∃ q : SortedFormula L E (FullRVVariables S Unit), q.IsQF ∧
        ∀ v, q.realize M v ↔ φ.realize M v)
    (t : Z .rv) (ht : SortedDefinableOver M S.carrier
      {x : ∀ s, RVVariables Unit s → Z s | x .rv () = t}) : t ∈ S.carrier .rv := by
  obtain ⟨q, _, hq⟩ := exists_rv_formula_of_definable S ht hQE
  let A : ∀ s, Set (Z s) := fun s => match s with
    | .vf => ∅
    | .rv => S.carrier .rv
  let rename : ∀ s, ReductRVVariables S Unit s → (A s : Type z) ⊕ RVVariables Unit s
    | .vf => PEmpty.elim
    | .rv => id
  apply hRV t
  refine ⟨q.relabel rename, fun x => ?_⟩
  have he : (fun s => Sum.elim (Subtype.val (p := (· ∈ A s))) (x s) ∘ rename s) =
      reductRVAssignment S (x .rv) := by
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => cases i <;> rfl
  exact (hq x).trans ((Iff.of_eq (congrArg (q.realize M) he.symm)).trans
    (q.realize_relabel (M := M) rename (fun s => Sum.elim Subtype.val (x s))).symm)

/-- The VF assertion of 3.6 and 3.19. The named RV parameters need not
have representatives in the base field. -/
theorem vf_definable_point_mem
    (hMove : ∀ a ∉ S.carrier .vf, ∃ e : SortedIsomorphism M M,
      e.toEmbedding .vf a ≠ a ∧ (∀ x ∈ S.carrier .vf, e.toEmbedding .vf x = x) ∧
        ∀ t, e.toEmbedding .rv t = t)
    (A : ∀ s, Set (Z s)) (hA : A .vf ⊆ S.carrier .vf) (a : Z .vf)
    (ha : SortedDefinableOver M A {x : ∀ s, UnaryVFVariables s → Z s | x .vf 0 = a}) :
    a ∈ S.carrier .vf := by
  let p : ∀ s, UnaryVFVariables s → Z s
    | .vf => fun _ => a
    | .rv => Empty.elim
  have he : {x : ∀ s, UnaryVFVariables s → Z s | x .vf 0 = a} = {p} := by
    ext x
    constructor
    · intro hx
      funext s i
      cases s with
      | vf => exact (congrArg (x .vf) (Fin.fin_one_eq_zero i)).trans hx
      | rv => exact i.elim
    · rintro rfl
      rfl
  rw [he] at ha
  exact vf_range_subset_of_definable_singleton_of_immediate_movers M S hMove hA ha ⟨0, rfl⟩

/-- The exchange step in removing a finite-radius disc parameter in 3.8.
Each center is a representative. Smallness gives a center outside cl(S,a). -/
theorem remove_disc_parameter {K : Type*} (base D : Set K) (cl : K → Set K) (a : K)
    (hex : ∀ x y, x ∈ cl y → x ∉ base → y ∈ cl x)
    (hrep : ∀ b ∈ D, a ∈ cl b) (hlarge : ¬ D ⊆ cl a) : a ∈ base := by
  by_contra ha
  exact hlarge (fun b hb => hex a b (hrep b hb) ha)

section ClosedDiscs

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- Lemma 3.20. Realizing the small cut above the radius (multiplicative
order) produces an outside point with the same translates over the base.
The last premise is invariance under the immediate isomorphism of Section 2. -/
theorem closedDisc_meets_base (F : Set K) (b : K) (r : O.ValueGroup)
    (hcut : (∀ c ∈ F, r < O.valuation (b - c)) →
      ∃ s, r < s ∧ ∀ c ∈ F, s < O.valuation (b - c))
    (hinv : ∀ a, (∀ c ∈ F, rv O (a - c) = rv O (b - c)) → a ∈ closedDisc O b r) :
    (F ∩ closedDisc O b r).Nonempty := by
  by_contra he
  have hfar (c : K) (hc : c ∈ F) : r < O.valuation (b - c) := by
    by_contra! h
    exact he ⟨c, hc, by
      change O.valuation (c - b) ≤ r
      rwa [← neg_sub, O.valuation.map_neg]⟩
  obtain ⟨s, hrs, hs⟩ := hcut hfar
  obtain ⟨d, hd⟩ := O.valuation_surjective s
  have hb := hinv (d + b) (by
    intro c hc
    have hn : b - c ≠ 0 := fun h => by simpa [h] using (zero_le.trans_lt (hfar c hc))
    apply (rv_eq_rv_iff_valuation O hn).mpr
    simpa only [sub_sub_sub_cancel_right, add_sub_cancel_right, hd] using hs c hc)
  change O.valuation (d + b - b) ≤ r at hb
  rw [add_sub_cancel_right, hd] at hb
  exact hrs.not_ge hb

end ClosedDiscs
end GeneralizedEuler.Section3
