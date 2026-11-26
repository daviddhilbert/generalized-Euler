module

public import Section5.GradedBlowupLabels
public import Section4.Objects
public import Section3.DefinableFunctions

/-! A definable focus on a pullback witnesses the deletion bound
required for the corresponding elementary blowup. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1))

/-- Over a representative of the retained labels, the leading terms
of the finitely many focus values contain all the possible deleted
labels. The focus is evaluated on the original RV tags. -/
theorem finite_deletion_of_finite_focus_image
    (j : Fin (k+1)) (focus : (Fin k → K) → U.carrier → K)
    (valid : ∀ (x : Fin k → K) (u : U.carrier),
      U.label u ∘ j.succAbove = rv O ∘ x → rv O (focus x u) = U.label u j)
    (finite : ∀ x, (Set.range (focus x)).Finite)
    (r : Fin k → RV0 O) :
    {t ∈ Set.range U.label | t ∘ j.succAbove = r}.Finite := by
  classical
  choose x hx using fun i => rv_surjective O (r i)
  have lab : rv O ∘ x = r := funext hx
  let D := {t ∈ Set.range U.label | t ∘ j.succAbove = r}
  let project (t : Fin (k+1) → RV0 O) := t j
  have injective : Set.InjOn project D := by
    rintro t ⟨_,ht⟩ u ⟨_,hu⟩ eq
    funext i
    by_cases he : i = j
    · subst i
      exact eq
    · obtain ⟨v,rfl⟩ := Fin.exists_succAbove_eq he
      exact congrFun (ht.trans hu.symm) v
  have ht := (finite x).image (rv O)
  apply ht.of_injOn (f := project) _ injective
  rintro _ ⟨⟨a,rfl⟩,ha⟩
  exact ⟨focus x a,Set.mem_range_self a,valid x a (ha.trans lab.symm)⟩

/-- Apply the relative RV-to-VF finiteness result to the focus graph
when it is given by finitely many leading-term tests in its field
output. The test functions are the field terms over the retained tuple. -/
theorem finite_deletion_of_focus_tests [TopologicalSpace K] [OrderTopology K]
    (j : Fin (k+1)) (focus : (Fin k → K) → U.carrier → K)
    (valid : ∀ (x : Fin k → K) (u : U.carrier),
      U.label u ∘ j.succAbove = rv O ∘ x → rv O (focus x u) = U.label u j)
    {I : Type} [Finite I] (g : I → (Fin k → K) → K → K)
    (graph : ∀ (x : Fin k → K) (u : U.carrier) (y : K),
      (∀ i, rv O (g i x y) = rv O (g i x (focus x u))) → y = focus x u)
    (finite : ∀ i x, (criticalSet (g i x)).Finite)
    {eps : K} (hp : 0 < eps) (hv : O.valuation eps < 1) :
    ∀ r : Fin k → RV0 O, {t ∈ Set.range U.label | t ∘ j.succAbove = r}.Finite :=
  finite_deletion_of_finite_focus_image O hO power S U j focus valid
    (finite_rv_to_field_image O hO hp hv focus g graph finite)

end GeneralizedEuler.Section5
