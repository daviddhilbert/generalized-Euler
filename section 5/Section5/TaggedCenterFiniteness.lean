module

public import Section5.StandardHeadContractions

/-! A fixed-base field-valued map of a remaining field tuple and
RV parameters takes only finitely many values for each field tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n : ℕ} {I : Type} [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem finite_tagged_center_range
    (hyp : HeadPreparationHypotheses O hO power S)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (c : (Fin n → K) → (I → RV0 O) → K)
    (defC : DefinableRelation 𝓜 S.carrier (fun (a : SortedAssignment Z (MixedVariables n I))
      (b : fieldAssignment 1 Z) => c (a .vf) (a .rv) = b .vf 0)) :
    ∀ b, (Set.range (c b)).Finite := by
  classical
  let G : Set (K × ((Fin n → K) × (I → RV0 O))) := {p | c p.2.1 p.2.2 = p.1}
  let ren : (s : TCsort) → SumVariables (MixedVariables n I) (MixedVariables 1 Empty) s → VerticalVariables n I s
    | .vf => Sum.elim Sum.inr (fun _ => .inl ())
    | .rv => Sum.elim id Empty.elim
  have d : SortedDefinableOver 𝓜 S.carrier {a : SortedAssignment Z (VerticalVariables n I) |
      (a .vf (.inl ()),a .vf ∘ Sum.inr,a .rv) ∈ G} := defC.pullback_relabel ren
  obtain ⟨C,hC⟩ := finite_vertical_centers O hO power S
    hyp.minusOne hyp.minusOne_realizes hyp.fieldTerms hyp.fieldTerms_realize
    (hyp.saturated n I inferInstance) (hyp.immediate n) G d
  intro b
  let centers (t : C) : K := t.val.realize 𝓜 (centerAssignment O hO power S b)
  apply (Set.finite_range centers).subset
  rintro _ ⟨u,rfl⟩
  let x := c b u
  by_contra h
  have ne (t : C) : x - centers t ≠ 0 := by
    intro e
    exact h ⟨t,(sub_eq_zero.1 e).symm⟩
  have existsSmall : ∃ d : K, d ≠ 0 ∧ ∀ t : C, O.valuation d < O.valuation (x-centers t) := by
    let : Fintype C := Fintype.ofFinite C
    by_cases hne : Nonempty C
    · let : Nonempty C := hne
      obtain ⟨a,_,least⟩ := (Finset.univ : Finset C).exists_min_image (fun t => O.valuation (x-centers t)) Finset.univ_nonempty
      refine ⟨eps * (x-centers a),mul_ne_zero he (ne a),?_⟩
      intro t
      have pos : 0 < O.valuation (x-centers a) := pos_iff_ne_zero.2 ((map_ne_zero _).2 (ne a))
      rw [map_mul]
      exact (mul_lt_mul_of_pos_right small pos).trans_le
        (by simpa only [one_mul] using least t (Finset.mem_univ t))
    · exact ⟨eps,he,fun t => (hne ⟨t⟩).elim⟩
  obtain ⟨e,he',min⟩ := existsSmall
  have same (t) (ht : t ∈ C) :
      rv O (x - t.realize 𝓜 (centerAssignment O hO power S b)) =
      rv O ((x+e) - t.realize 𝓜 (centerAssignment O hO power S b)) := by
    change rv O (x-centers ⟨t,ht⟩) = rv O ((x+e)-centers ⟨t,ht⟩)
    symm
    apply (rv_eq_rv_iff_valuation O (ne ⟨t,ht⟩)).2
    rw [add_sub_right_comm,add_comm (x-centers ⟨t,ht⟩),add_sub_cancel_right]
    exact min ⟨t,ht⟩
  have moved := (hC b x (x+e) u same).1 (show (x,b,u) ∈ G from rfl)
  change x = x+e at moved
  exact he' (add_left_cancel (moved.symm.trans (add_zero x).symm))

end GeneralizedEuler.Section5
