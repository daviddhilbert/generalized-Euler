module

public import Section5.FixedBaseCenters
public import Section5.DefinableRelations

/-! A fixed-base definable function from RV tuples to the field has
finite image by preparing its graph with the finite-center criterion. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem finite_definable_rv_field_image
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier I)
      (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (f : (I → RV0 O) → K)
    (graph : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I) | a .vf 0 = f (a .rv)}) :
    ∃ C : Finset (S.carrier .vf), Set.range f ⊆ Subtype.val '' (↑C : Set (S.carrier .vf)) := by
  classical
  let D := {p : K × (I → RV0 O) | p.1 = f p.2}
  obtain ⟨C,hC⟩ := finite_centers_of_definable O hO power S minusOne hm F hF sat immediate D graph
  refine ⟨C,?_⟩
  rintro _ ⟨t,rfl⟩
  let x := f t
  by_contra out
  have ne (c : S.carrier .vf) (hc : c ∈ C) : x - c.val ≠ 0 := by
    intro h
    exact out ⟨c,hc,(sub_eq_zero.1 h).symm⟩
  have perturbation : ∃ d : K, d ≠ 0 ∧ ∀ c ∈ C, O.valuation d < O.valuation (x - c.val) := by
    by_cases hn : C.Nonempty
    · obtain ⟨a,ha,hmin⟩ := C.exists_min_image (fun c => O.valuation (x-c.val)) hn
      refine ⟨eps*(x-a.val),mul_ne_zero he (ne a ha),fun c hc => ?_⟩
      have pos : 0 < O.valuation (x-a.val) := pos_iff_ne_zero.2 ((map_ne_zero _).2 (ne a ha))
      rw [map_mul]
      exact ((mul_lt_mul_of_pos_right small pos).trans_le (by simpa only [one_mul] using hmin c hc))
    · exact ⟨eps,he,fun c hc => (hn ⟨c,hc⟩).elim⟩
  obtain ⟨d,hd,hdv⟩ := perturbation
  have same (c : S.carrier .vf) (hc : c ∈ C) : rv O (x-c.val) = rv O ((x+d)-c.val) := by
    symm
    apply (rv_eq_rv_iff_valuation O (ne c hc)).2
    rw [add_sub_right_comm,add_comm (x-c.val),add_sub_cancel_right]
    exact hdv c hc
  have yes : (x,t) ∈ D := rfl
  have mem := (hC x (x+d) t same).1 yes
  change x+d = x at mem
  exact hd (add_left_cancel (mem.trans (add_zero _).symm))

end GeneralizedEuler.Section5
