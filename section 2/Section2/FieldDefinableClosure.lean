module

public import Section2.ConvexLanguage
public import Mathlib.ModelTheory.Substructures
public import Mathlib.Combinatorics.Matroid.Rank.ENat

/-! Definable field closure in a universal theory with quantifier
elimination, and the rank-one residue generation argument. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v

variable {L : Language.{u, v}} {K : Type*} [L.Structure K]

/-- In a universal theory with QE, a point uniquely defined over a
nonempty parameter tuple is the value of a term over that tuple. -/
theorem exists_term_of_uniquely_definable {T : L.Theory} [T.IsUniversal] [K ⊨ T] [Nonempty K]
    (hQE : EliminatesQuantifiers T) {V : Type*} [Nonempty V] (p : V → K)
    (a : K) (φ : L.Formula (V ⊕ Unit))
    (hφ : ∀ x : K, φ.Realize (Sum.elim p (fun _ => x)) ↔ x = a) :
    ∃ t : L.Term V, t.realize p = a := by
  let B := Substructure.closure L (Set.range p)
  let g (i : V) : B := ⟨p i, Substructure.subset_closure (Set.mem_range_self i)⟩
  let : Nonempty B := (inferInstance : Nonempty V).map g
  let e : B ↪ₑ[L] K := elementaryEmbeddingOfQE hQE B.subtype
  let ψ := φ.iExs Unit
  have he (i : V) : e (g i) = p i := rfl
  have hK : ψ.Realize (e ∘ g) := by
    rw [show e ∘ g = p from funext he, Formula.realize_iExs]
    exact ⟨fun _ => a, (hφ a).mpr rfl⟩
  obtain ⟨b, hb⟩ := Formula.realize_iExs.mp ((e.map_formula ψ g).mp hK)
  have h := (e.map_formula φ (Sum.elim g b)).mpr hb
  have heq : e ∘ Sum.elim g b = Sum.elim p (fun _ => e (b ())) := by
    funext i
    cases i with
    | inl i => exact he i
    | inr i => cases i; rfl
  rw [heq, hφ] at h
  have hmem : a ∈ (B : Set K) := h ▸ (b ()).property
  change a ∈ (Substructure.closure L (Set.range p) : Set K) at hmem
  rw [Substructure.coe_closure_eq_range_term_realize] at hmem
  obtain ⟨t, ht⟩ := hmem
  let pick (i : Set.range p) : V := i.property.choose
  have hp : p ∘ pick = Subtype.val := funext (fun i => i.property.choose_spec)
  exact ⟨t.relabel pick, by rw [Term.realize_relabel, hp]; exact ht⟩

/-- A nonloop generates a rank-at-most-one extension over the base. -/
theorem matroid_closure_singleton_of_rank_le_one (B : Matroid K) (hrank : B.eRk B.E ≤ 1)
    {a : K} (ha : B.IsNonloop a) : B.closure {a} = B.E := by
  have hsub : {a} ⊆ B.E := Set.singleton_subset_iff.mpr ha.mem_ground
  have hRankFinite := B.isRkFinite_of_finite (Set.finite_singleton a)
  have h := hRankFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk hsub (ha.eRk_eq.symm ▸ hrank)
  simpa only [B.closure_ground] using h

/-- Relative rank at most one and a genuinely new residue give term
generation over the old residue parameters and that residue. -/
theorem exists_residue_term_of_relative_rank_le_one
    {T : L.Theory} [T.IsUniversal] [K ⊨ T] [Nonempty K] (hQE : EliminatesQuantifiers T)
    (old : Set K) (a : K) (B : Matroid K) (hFull : B.E = Set.univ)
    (hrank : B.eRk B.E ≤ 1) (ha : B.IsNonloop a)
    (hClosure : ∀ x ∈ B.closure {a}, ∃ φ : L.Formula ((old ⊕ Unit) ⊕ Unit),
      ∀ y : K, φ.Realize (Sum.elim (Sum.elim Subtype.val (fun _ => a)) (fun _ => y)) ↔ y = x)
    (x : K) :
    ∃ t : L.Term (old ⊕ Unit), t.realize (Sum.elim Subtype.val (fun _ => a)) = x := by
  have hm : x ∈ B.closure {a} := by
    rw [matroid_closure_singleton_of_rank_le_one B hrank ha, hFull]
    exact Set.mem_univ x
  obtain ⟨φ, hφ⟩ := hClosure x hm
  exact exists_term_of_uniquely_definable hQE _ x φ hφ

end GeneralizedEuler.Section2
