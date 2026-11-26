module

public import Section5.PreparationGraph

/-! Lemma 5.4: unary deformation into an RV-pullback over the fixed base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type}

local notation "M" => canonicalStructure (L := L) O hO power

set_option linter.style.haveILetI false in
/-- Lemma 5.4. One sequence of fixed-base special transformations works
for the entire family, leaving the original RV tuple unchanged. The map
is the restriction of the definable map on the full affine line. -/
theorem unary_deformation
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes M (CenterTestVariables S.carrier I)
      (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism M M, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set (K × (I → RV0 O)))
    (hA : SortedDefinableOver M S.carrier {a : ∀ s, MixedVariables 1 I s → CanonicalSort O s |
      (a .vf 0, a .rv) ∈ A}) :
    ∃ cs : List (S.carrier .vf),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      SortedDefinableOver M S.carrier
        {v : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → CanonicalSort O s |
          P.map (v .vf 0) = (v .vf 1, decodeHistory O cs.length (v .rv))} ∧
      Function.Injective (fun p : K × (I → RV0 O) => (P.map p.1, p.2)) ∧
      (∀ x y ξ, P.label x = P.label y → ((x, ξ) ∈ A ↔ (y, ξ) ∈ A)) ∧
      (fun p : K × (I → RV0 O) => (P.map p.1, p.2)) '' A =
        {p | rv O p.1.1 = P.lead p.1.2 ∧ ∃ x, (x, p.2) ∈ A ∧ P.label x = p.1.2} := by
  classical
  obtain ⟨C, hC⟩ := finite_centers_of_definable O hO power S minusOne hm F hF sat immediate A hA
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val C.toList
  have hA' : ∀ x y ξ, P.label x = P.label y → ((x, ξ) ∈ A ↔ (y, ξ) ∈ A) := by
    intro x y ξ he
    have h := ((UnaryPreparation.regularize (O := O)).prepare_decides Subtype.val C.toList he).2
    exact hC x y ξ fun c hc => h c (Finset.mem_toList.mpr hc)
  refine ⟨C.toList, preparationGraph_definable O hO power S F minusOne hm hF _, ?_, hA', ?_⟩
  · intro p q eq
    obtain ⟨hp, hξ⟩ := Prod.mk.inj eq
    exact Prod.ext (UnaryPreparation.map_injective _ hp) hξ
  · exact P.image_restriction A hA'

set_option linter.style.haveILetI false in
/-- One finite sequence works for all tests in a finite family. Each
test retains its entire RV tuple as free variables. -/
theorem unary_preparation_of_indexed_tests {J : Type*} [Finite J] (I : J → Type)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ j, RealizesFinitelySatisfiableTypes M (CenterTestVariables S.carrier (I j))
      (CenterTestAssignments S.carrier (I j)))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism M M, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : ∀ j, Set (K × (I j → RV0 O)))
    (hA : ∀ j, SortedDefinableOver M S.carrier {a : ∀ s, MixedVariables 1 (I j) s → CanonicalSort O s |
      (a .vf 0, a .rv) ∈ A j}) :
    ∃ cs : List (S.carrier .vf),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      SortedDefinableOver M S.carrier
        {v : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → CanonicalSort O s |
          P.map (v .vf 0) = (v .vf 1, decodeHistory O cs.length (v .rv))} ∧
      ∀ j x y ξ, P.label x = P.label y → ((x, ξ) ∈ A j ↔ (y, ξ) ∈ A j) := by
  classical
  letI := Fintype.ofFinite J
  have hex (j : J) := finite_centers_of_definable O hO power S minusOne hm F hF (sat j) immediate (A j) (hA j)
  choose C hC using hex
  let all := Finset.univ.biUnion C
  refine ⟨all.toList, preparationGraph_definable O hO power S F minusOne hm hF _, ?_⟩
  intro j x y ξ he
  have h := ((UnaryPreparation.regularize (O := O)).prepare_decides Subtype.val all.toList he).2
  apply hC j x y ξ
  intro c hc
  exact h c (Finset.mem_toList.mpr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hc⟩))

theorem unary_preparation_of_finite_family {J : Type*} [Finite J]
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes M (CenterTestVariables S.carrier I)
      (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism M M, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : J → Set (K × (I → RV0 O)))
    (hA : ∀ j, SortedDefinableOver M S.carrier {a : ∀ s, MixedVariables 1 I s → CanonicalSort O s |
      (a .vf 0, a .rv) ∈ A j}) :
    ∃ cs : List (S.carrier .vf),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      SortedDefinableOver M S.carrier
        {v : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → CanonicalSort O s |
          P.map (v .vf 0) = (v .vf 1, decodeHistory O cs.length (v .rv))} ∧
      ∀ j x y ξ, P.label x = P.label y → ((x, ξ) ∈ A j ↔ (y, ξ) ∈ A j) :=
  unary_preparation_of_indexed_tests O hO power S (fun _ : J => I) minusOne hm F hF (fun _ => sat) immediate A hA

end GeneralizedEuler.Section5
