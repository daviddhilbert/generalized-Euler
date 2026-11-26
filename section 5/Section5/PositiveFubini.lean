module

public import Section5.InnerIntegralFiberClasses
public import Section5.RelativePositiveIntegration

/-! The positive outer integral of the representative obtained by
integrating along a field projection is the integral of the total lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {q m b n b' n' : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem projection_inner_representative_total_class
    (e : Fin (b+n) ≃ Fin q)
    (A : Set (SortedAssignment Z (MixedVariables q (Fin m))))
    (d : SortedDefinableOver 𝓜 S.carrier A)
    (finite : ∀ x : Fin q → K, {r | (x,r) ∈ mixedTuple '' A}.Finite)
    (C : GradedLiftCover 𝓜 S (fieldProjection (splitFieldSpace e A)) (splitFieldSpace e A) (baseRVZero S)) :
    C.representative.totalLiftClass (fieldProjection_definable (splitFieldSpace_definable e d)) =
      fieldClass 𝓜 S (mixedFieldObject S A d finite) := by
  let B := splitFieldSpace e A
  let D := fieldProjection B
  have defB := splitFieldSpace_definable e d
  have defD := fieldProjection_definable defB
  let fib (p : fieldAssignment b Z) (_ : p ∈ D) := splitFieldSpace_finite_fibers e finite p
  have i := C.representative_total_class defD defB fib
  let F := mixedFieldObject S (totalMixedSet (onlyOver D B))
    (totalMixedSet_definable (onlyOver_definable defD defB)) (totalMixedSet_finite fib)
  exact i.trans (fieldClass_of_iso 𝓜 S (A := F) (B := mixedFieldObject S A d finite)
    (splitFieldSpace_total_iso e d).symm)

theorem projection_inner_integral_fiber_class
    (e : Fin (b+n) ≃ Fin q)
    (A : Set (SortedAssignment Z (MixedVariables q (Fin m))))
    (d : SortedDefinableOver 𝓜 S.carrier A)
    (finite : ∀ x : Fin q → K, {r | (x,r) ∈ mixedTuple '' A}.Finite)
    (C : GradedLiftCover 𝓜 S (fieldProjection (splitFieldSpace e A)) (splitFieldSpace e A) (baseRVZero S))
    (p : fieldProjection (splitFieldSpace e A))
    (H : IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val)) :
    relativeFunctionFiberClass S neg _ C.representative p =
      (positiveLiftEquiv (relativeBase S p.val) (relativeBase_neg S neg p.val) H).symm
        (fieldClass 𝓜 (relativeBase S p.val)
          (mixedFieldObject (relativeBase S p.val) _
            (definable_scheme_at_fiber p.val _ (splitFieldSpace_definable e d))
            (splitFieldSpace_finite_fibers e finite p.val))) := by
  apply (positiveLiftEquiv (relativeBase S p.val) (relativeBase_neg S neg p.val) H).injective
  rw [RingEquiv.apply_symm_apply]
  exact (relativeFunctionFiberClass_lift S neg _ C.representative p H).trans
    (C.representative_fiber_lift_class rfl (splitFieldSpace_definable e d) p
      (splitFieldSpace_finite_fibers e finite p.val))

theorem projection_fubini_positive_integrals
    (H : IntegrationHypotheses S neg)
    (e : Fin (b+n) ≃ Fin q) (e' : Fin (b'+n') ≃ Fin q)
    (A : Set (SortedAssignment Z (MixedVariables q (Fin m))))
    (d : SortedDefinableOver 𝓜 S.carrier A)
    (finite : ∀ x : Fin q → K, {r | (x,r) ∈ mixedTuple '' A}.Finite)
    (C : GradedLiftCover 𝓜 S (fieldProjection (splitFieldSpace e A)) (splitFieldSpace e A) (baseRVZero S))
    (C' : GradedLiftCover 𝓜 S (fieldProjection (splitFieldSpace e' A)) (splitFieldSpace e' A) (baseRVZero S))
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables b Empty))
      (BaseAssignments S.carrier (MixedVariables b Empty)))
    (sat' : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables b' Empty))
      (BaseAssignments S.carrier (MixedVariables b' Empty)))
    (fiber : ∀ p : fieldProjection (splitFieldSpace e A),
      IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val))
    (fiber' : ∀ p : fieldProjection (splitFieldSpace e' A),
      IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val)) :
    relativePositiveIntegral S neg _ H sat (fieldProjection_definable (splitFieldSpace_definable e d))
      fiber (Quotient.mk _ C.representative) =
    relativePositiveIntegral S neg _ H sat' (fieldProjection_definable (splitFieldSpace_definable e' d))
      fiber' (Quotient.mk _ C'.representative) := by
  rw [relativePositiveIntegral_mk,relativePositiveIntegral_mk]
  exact congrArg (positiveLiftEquiv S neg H).symm
    ((projection_inner_representative_total_class S e A d finite C).trans
      (projection_inner_representative_total_class S e' A d finite C').symm)

end GeneralizedEuler.Section5
