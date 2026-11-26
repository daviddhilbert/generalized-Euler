module

public import Section5.RelativeGradedLiftSchemes
public import Section5.FieldClassPreparation

/-! Generalize the pieces and objects of a local graded lift
presentation to formula schemes over the original parameter base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P U : TCsort → Type}

theorem relative_graded_scheme_of_generated_partition (p : SortedAssignment X P)
    (A : Set (SortedAssignment X (SumVariables P U)))
    (zero : S.carrier .rv) (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (sat : ∀ k, let T := M.termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes M (WithBase T.carrier (RVVariables (Fin k)))
        (BaseAssignments T.carrier (RVVariables (Fin k))))
    {I : Type} [Finite I]
    (V : I → GradedObject M (M.termGenerated (namedTuple S p)))
    (D : I → Set (SortedAssignment X U))
    (hD : ∀ i, SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier (D i) ∧
      MixedDefinablyEquivalent M (M.termGenerated (namedTuple S p)) (D i) (ObjectLift.carrier (V i).2))
    (disj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (cover : (⋃ i, D i) = {u | appendAssignments p u ∈ A}) :
    ∃ W : RelativeGradedLiftScheme M S P U, W.valid zero A p := by
  classical
  let N := M.termGenerated (namedTuple S p)
  let := Fintype.ofFinite I
  let e := (Fintype.equivFin I).symm
  have generalize_set (i : I) := definable_fiber_as_scheme p (D i) (hD i).1
  choose outputs defOut eqOut using generalize_set
  have witness (i : I) : ∃ W : RelativeRVLiftScheme M S P U, W.valid (outputs i) zero p := by
    obtain ⟨f,hf⟩ := (hD i).2
    have eq : {u | appendAssignments p u ∈ outputs i} = D i := Set.ext (eqOut i)
    let g := (Set.equivOfEq eq).trans f
    have hg : DefinableRelation M N.carrier
        (fun a b => ∃ ha : appendAssignments p a ∈ outputs i, (g ⟨a,ha⟩).val = b) := by
      refine hf.congr ?_
      intro a b
      constructor
      · rintro ⟨mem,h⟩
        exact ⟨(eqOut i a).2 mem,h⟩
      · rintro ⟨mem,h⟩
        exact ⟨(eqOut i a).1 mem,h⟩
    obtain ⟨bound,hBound⟩ := rvObject_uniform_label_bound (V i).2 (sat (V i).1)
    exact relativeRVLiftScheme_of_object (outputs i) p zero hzero (V i).2 g hg bound hBound
  choose objects valid using witness
  let W : RelativeGradedLiftScheme M S P U := ⟨_,outputs ∘ e,fun i => defOut (e i),objects ∘ e⟩
  refine ⟨W,?_,?_,fun i => valid (e i)⟩
  · intro u
    constructor
    · intro hu
      have hu' : u ∈ ⋃ i, D i := cover.symm ▸ hu
      obtain ⟨i,mem⟩ := Set.mem_iUnion.1 hu'
      refine ⟨e.symm i,?_⟩
      change appendAssignments p u ∈ outputs (e (e.symm i))
      rw [e.apply_symm_apply]
      exact (eqOut i u).2 mem
    · rintro ⟨i,hi⟩
      have hu : u ∈ ⋃ j, D j := Set.mem_iUnion.2 ⟨e i,(eqOut (e i) u).1 hi⟩
      have h : u ∈ {u | appendAssignments p u ∈ A} := cover ▸ hu
      exact h
  · intro i j ne u h
    exact Set.disjoint_left.1 (disj (e.injective.ne ne)) ((eqOut (e i) u).1 h.1) ((eqOut (e j) u).1 h.2)

section Canonical

open FirstOrder.Language

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n : ℕ} {I : Type} [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "W" => MixedVariables n I

/-- Uniformly choose a finite graded family representing the lift
of each retained fiber, allowing the degrees and arities to vary. -/
theorem uniform_relative_mixed_lifts
    (D : Set (SortedAssignment (CanonicalSort O) P)) (defD : SortedDefinableOver 𝓜 S₀.carrier D)
    (A : Set (SortedAssignment (CanonicalSort O) (SumVariables P W))) (defA : SortedDefinableOver 𝓜 S₀.carrier A)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S₀.carrier P) (BaseAssignments S₀.carrier P))
    (localSat : ∀ p ∈ D, ∀ (j : ℕ) (J : Type), Finite J →
      let T := (𝓜).termGenerated (namedTuple S₀ p)
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (VerticalPairVariables j J))
        (BaseAssignments T.carrier (VerticalPairVariables j J)))
    (localLabels : ∀ p ∈ D, ∀ k, let T := (𝓜).termGenerated (namedTuple S₀ p)
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin k)))
        (BaseAssignments T.carrier (RVVariables (Fin k))))
    (immediate : ∀ p ∈ D, ∀ j (b : Fin j → K) (x y : K),
      let T := (𝓜).termGenerated (namedTuple S₀ p)
      let B := (𝓜).termGenerated (centerAssignment O hO power T b)
      (∀ c : B.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
        ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
          (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (finite : ∀ p ∈ D, ∀ x : Fin n → K,
      {r | (x,r) ∈ mixedTuple '' {u : SortedAssignment (CanonicalSort O) W | appendAssignments p u ∈ A}}.Finite) :
    let zero : S₀.carrier .rv := ⟨(𝓜).funMap .rvZero (fun i => i.elim0),
      S₀.closed .rvZero _ (fun i => i.elim0)⟩
    ∃ (C : Finset (RelativeGradedLiftScheme 𝓜 S₀ P W)) (pieces : {i // i ∈ C} → Set (SortedAssignment (CanonicalSort O) P)),
      (∀ i, SortedDefinableOver 𝓜 S₀.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid zero A p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D := by
  intro zero
  apply uniform_graded_relative_lift_schemes sat zero D defD A defA
  intro p hp
  let T := (𝓜).termGenerated (namedTuple S₀ p)
  let B := {u : SortedAssignment (CanonicalSort O) W | appendAssignments p u ∈ A}
  have hd := definable_scheme_at_fiber p A defA
  obtain ⟨U,R,hR,disj,cover⟩ := mixed_set_partition_into_lifts O hO power T minusOne hm F hF
    (localSat p hp) (immediate p hp) B hd (finite p hp)
  exact relative_graded_scheme_of_generated_partition p A zero rfl (localLabels p hp) U R hR disj cover

end Canonical

end GeneralizedEuler.Section5
