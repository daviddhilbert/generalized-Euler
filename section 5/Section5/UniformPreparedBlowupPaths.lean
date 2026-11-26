module

public import Section5.PreparedCommonBlowup

/-! Choose whole local common-blowup paths on finitely many definable
pieces, then prepare all their defining formulas simultaneously. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language
  RelativeObjectFamily RelativeRVTest

universe z

namespace RelativeRVTest

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}

@[expose] def ofBase {D : Set (SortedAssignment X P)}
    (defD : SortedDefinableOver M S.carrier D) : RelativeRVTest M S P :=
  ofSet (defD.pullback_relabel (fun s => (Sum.inl : P s → SumVariables P (RVVariables Empty) s)))

theorem same_ofBase {D : Set (SortedAssignment X P)} (defD : SortedDefinableOver M S.carrier D)
    {p p' : SortedAssignment X P} (eq : (ofBase defD).Same p p') :
    p ∈ D ↔ p' ∈ D := by
  let nil : SortedAssignment X (RVVariables Empty)
    | .vf => PEmpty.elim
    | .rv => Empty.elim
  exact eq nil

end RelativeRVTest

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty

set_option maxHeartbeats 500000 in
theorem uniform_prepared_blowup_paths
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (satCover : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (satTests : ∀ (I : Type), Finite I → RealizesFinitelySatisfiableTypes 𝓜
      (CenterTestVariables S.carrier I) (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    {A : RelativeObjectFamily 𝓜 S P (Fin a)} {B : RelativeObjectFamily 𝓜 S P (Fin b)}
    (zero : S.carrier .rv) (hz : zero.val = 0)
    (vA : ∀ p ∈ D, Valid A zero p) (vB : ∀ p ∈ D, Valid B zero p)
    (satLocal : ∀ p ∈ D, ∀ d, let T := (𝓜).termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase T.carrier (RVVariables (Fin d)))
        (BaseAssignments T.carrier (RVVariables (Fin d))))
    (localCommon : ∀ p (hp : p ∈ D), let T := (𝓜).termGenerated (namedTuple S p)
      let nT : rv O (-1) ∈ T.carrier .rv :=
        ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property
      CommonBlowup (ElementaryClassStep O hO power T nT) (fiberClass A zero hz p (vA p hp))
        (fiberClass B zero hz p (vB p hp))) :
    ∃ (C : Finset (RelativeCommonBlowupScheme neg A B)) (pieces : {i // i ∈ C} → Set (SortedAssignment Z P))
      (cs : List (S.carrier .vf)),
      let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      (∀ i, SortedDefinableOver 𝓜 S.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid zero p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D ∧
      ∀ i (p p' : SortedAssignment Z P), T.label (p .vf 0) = T.label (p' .vf 0) →
        (p ∈ pieces i ↔ p' ∈ pieces i) ∧ Agree i.val.tests p p' := by
  have localNamed p hp := relative_common_blowup_scheme_of_classes (neg := neg) p zero hz (satLocal p hp)
    (vA p hp) (vB p hp) (localCommon p hp)
  obtain ⟨C,pieces,defPieces,valid,disjoint,cover⟩ :=
    uniform_relative_common_blowup_schemes satCover zero D defD localNamed
  let J := {i // i ∈ C}
  let tests (i : J) := ofBase (defPieces i) :: i.val.tests
  obtain ⟨cs,same⟩ := prepare_relative_rv_tests O hO power S (ofFamily tests) F minusOne hm hF satTests immediate
  refine ⟨C,pieces,cs,defPieces,valid,disjoint,cover,?_⟩
  intro i p p' he
  have h : Agree (tests i) p p' := agree_family tests (same p p' he) i
  refine ⟨same_ofBase (defPieces i) (h (ofBase (defPieces i)) (List.mem_cons_self ..)),?_⟩
  exact fun W hW => h W (List.mem_cons_of_mem _ hW)

end GeneralizedEuler.Section5
