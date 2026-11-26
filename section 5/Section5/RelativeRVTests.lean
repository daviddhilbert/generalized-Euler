module

public import Section5.RelativeSchemeDescent
public import Section5.UnaryWitnessPreparation
public import Section5.PreparedUnaryRVIndex

/-! Store finitely many relative RV formulas of varying arity in a
single test list. A unary preparation can make all their fibers
constant at once. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}

structure RelativeRVTest (M : SortedStructure L E X) (S : SortedSubstructure M) (P : TCsort → Type) where
  vars : Type
  finite : Finite vars
  set : Set (SortedAssignment X (SumVariables P (RVVariables vars)))
  definable : SortedDefinableOver M S.carrier set

namespace RelativeRVTest

@[expose] def ofSet {I : Type} [Finite I]
    {D : Set (SortedAssignment X (SumVariables P (RVVariables I)))}
    (defD : SortedDefinableOver M S.carrier D) : RelativeRVTest M S P := ⟨I,inferInstance,D,defD⟩

@[expose] def Same (T : RelativeRVTest M S P) (p p' : SortedAssignment X P) : Prop :=
  ∀ a, appendAssignments p a ∈ T.set ↔ appendAssignments p' a ∈ T.set

abbrev Agree (tests : List (RelativeRVTest M S P)) (p p' : SortedAssignment X P) : Prop :=
  ∀ T ∈ tests, Same T p p'

theorem agree_append {A B : List (RelativeRVTest M S P)} {p p' : SortedAssignment X P} :
    Agree (A++B) p p' ↔ Agree A p p' ∧ Agree B p p' := by
  simp only [Agree,List.mem_append,or_imp,forall_and]

def graphVars (P : TCsort → Type) (I J : Type) :
    (s : TCsort) → SumVariables (SumVariables P (RVVariables I)) (RVVariables J) s →
      SumVariables P (RVVariables (I ⊕ J)) s
  | .vf => Sum.elim (Sum.elim Sum.inl PEmpty.elim) PEmpty.elim
  | .rv => Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)

@[expose] def ofGraph {I J : Type} [Finite I] [Finite J]
    {G : Set (SortedAssignment X (SumVariables (SumVariables P (RVVariables I)) (RVVariables J)))}
    (defG : SortedDefinableOver M S.carrier G) : RelativeRVTest M S P :=
  ofSet (defG.pullback_relabel (graphVars P I J))

theorem same_ofGraph {I J : Type} [Finite I] [Finite J]
    {G : Set (SortedAssignment X (SumVariables (SumVariables P (RVVariables I)) (RVVariables J)))}
    (defG : SortedDefinableOver M S.carrier G) {p p' : SortedAssignment X P}
    (same : (ofGraph defG).Same p p')
    (a : SortedAssignment X (RVVariables I)) (b : SortedAssignment X (RVVariables J)) :
    appendAssignments (appendAssignments p a) b ∈ G ↔ appendAssignments (appendAssignments p' a) b ∈ G := by
  let u : SortedAssignment X (RVVariables (I ⊕ J))
    | .vf => PEmpty.elim
    | .rv => Sum.elim (a .rv) (b .rv)
  have pack (x : SortedAssignment X P) :
      (fun s => appendAssignments x u s ∘ graphVars P I J s) = appendAssignments (appendAssignments x a) b := by
    funext s i
    rcases i with (i | i) | i
    · cases s <;> rfl
    · cases s
      · exact i.elim
      · rfl
    · cases s
      · exact i.elim
      · rfl
  have eq := same u
  change (fun s => appendAssignments p u s ∘ graphVars P I J s) ∈ G ↔
    (fun s => appendAssignments p' u s ∘ graphVars P I J s) ∈ G at eq
  simpa only [pack] using eq

end RelativeRVTest

section Unary

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty

theorem prepare_relative_rv_tests
    (tests : List (RelativeRVTest 𝓜 S U))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ (I : Type), Finite I → RealizesFinitelySatisfiableTypes 𝓜
      (CenterTestVariables S.carrier I) (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t) :
    ∃ cs : List (S.carrier .vf),
      let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ p p' : SortedAssignment Z U, T.label (p .vf 0) = T.label (p' .vf 0) →
        RelativeRVTest.Agree tests p p' := by
  classical
  let J := {T // T ∈ tests.toFinset}
  let I (j : J) := j.val.vars
  obtain ⟨cs,_,same,_⟩ := unary_preparation_of_witness_schemes O hO power S I F minusOne hm hF
    (fun j => sat (I j) j.val.finite) immediate (fun j : J => j.val.set) (fun j => j.val.definable)
  refine ⟨cs,?_⟩
  intro T p p' eq test mem a
  let j : J := ⟨test,List.mem_toFinset.2 mem⟩
  let q : SortedAssignment Z (RVVariables (HistoryIndex cs.length))
    | .vf => PEmpty.elim
    | .rv => encodeHistory O cs.length (T.label (p .vf 0))
  have h : T.label (p .vf 0) = decodeHistory O cs.length (q .rv) :=
    (decode_encode_history O cs.length _).symm
  exact (same j p q h a).symm.trans (same j p' q (eq.symm.trans h) a)

end Unary

end GeneralizedEuler.Section5
