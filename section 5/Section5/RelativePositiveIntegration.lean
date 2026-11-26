module

public import Section5.RelativeRVFunctions
public import Section5.IntegrationIsomorphism

/-! Positive relative integration descends to the quotient by
fiberwise equality of RV classes. The base of the function is fixed. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables b Empty
local notation "Q" => (gradedBlowupCongruence O hO power S neg)

variable (D : Set (fieldAssignment b (CanonicalSort O)))

@[expose] def relativeBase (p : fieldAssignment b Z) : SortedSubstructure 𝓜 :=
  (𝓜).termGenerated (namedTuple S p)

include neg in
omit [TopologicalSpace K] in
theorem relativeBase_neg (p : fieldAssignment b Z) : rv O (-1) ∈ (relativeBase S p).carrier .rv :=
  ((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property

local notation "R" => RelativeRVFunctionRepresentative 𝓜 S b D (baseRVZero S)

@[expose] def relativeFunctionFiberClass (F : R) (p : D) :
    (gradedBlowupCongruence O hO power (relativeBase S p.val) (relativeBase_neg S neg p.val)).Quotient :=
  (gradedBlowupCongruence O hO power (relativeBase S p.val) (relativeBase_neg S neg p.val)).mk'
    (F.fiberClass (by rfl) p)

@[expose] def relativeFunctionSetoid : Setoid R where
  r F G := ∀ p : D, relativeFunctionFiberClass S neg D F p = relativeFunctionFiberClass S neg D G p
  iseqv := ⟨fun _ _ => rfl,fun h p => (h p).symm,fun h g p => (h p).trans (g p)⟩

abbrev RelativePositiveFunction := Quotient (relativeFunctionSetoid S neg D)

theorem relativeFunctionFiberClass_lift (F : R) (p : D)
    (H : IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val)) :
    (positiveLiftEquiv (relativeBase S p.val) (relativeBase_neg S neg p.val) H)
      (relativeFunctionFiberClass S neg D F p) = ∑ i, liftObjectClass (F.fiberObject (by rfl) p i) := by
  have eval := positiveLiftEquiv_mk (relativeBase S p.val) (relativeBase_neg S neg p.val) H
    (F.fiberClass (by rfl) p)
  refine eval.trans ?_
  unfold RelativeRVFunctionRepresentative.fiberClass
  exact (map_sum (liftClassHom H.liftIso)
    (fun i => objectClass 𝓜 (relativeBase S p.val) (F.fiberObject (by rfl) p i)) Finset.univ).trans
    (Finset.sum_congr rfl (fun i _ => liftClassHom_class H.liftIso _))

theorem relative_total_class_of_pointwise_eq
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (d : SortedDefinableOver 𝓜 S.carrier D)
    (fiberInputs : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val))
    {F G : R} (eq : (relativeFunctionSetoid S neg D).r F G) :
    F.totalLiftClass d = G.totalLiftClass d := by
  apply F.totalLiftClass_eq_of_fiber_lift_eq rfl G sat d
  intro p
  let H := fiberInputs p
  have f := relativeFunctionFiberClass_lift S neg D F p H
  have g := relativeFunctionFiberClass_lift S neg D G p H
  exact f.symm.trans ((congrArg (positiveLiftEquiv _ _ H) (eq p)).trans g)

def relativePositiveIntegral
    (H : IntegrationHypotheses S neg)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (d : SortedDefinableOver 𝓜 S.carrier D)
    (fiberInputs : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val)) :
    RelativePositiveFunction S neg D → (Q).Quotient :=
  Quotient.lift (fun F : R => (positiveLiftEquiv S neg H).symm (F.totalLiftClass d))
    (fun _ _ eq => congrArg (positiveLiftEquiv S neg H).symm
      (relative_total_class_of_pointwise_eq S neg D sat d fiberInputs eq))

theorem relativePositiveIntegral_mk
    (H : IntegrationHypotheses S neg)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (d : SortedDefinableOver 𝓜 S.carrier D)
    (fiberInputs : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val))
    (F : R) :
    relativePositiveIntegral S neg D H sat d fiberInputs (Quotient.mk _ F) =
      (positiveLiftEquiv S neg H).symm (F.totalLiftClass d) := by
  unfold relativePositiveIntegral
  rfl

end GeneralizedEuler.Section5
