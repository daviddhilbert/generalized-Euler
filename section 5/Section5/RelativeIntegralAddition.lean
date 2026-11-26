module

public import Section5.RelativePositiveIntegration

/-! Tagged disjoint union represents addition of relative functions.
Positive integration preserves the empty family and tagged sums. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

namespace RelativeRVFunctionRepresentative

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {b : ℕ}
  {D : Set (fieldAssignment b X)} {zero : S.carrier .rv}
  (F G : RelativeRVFunctionRepresentative M S b D zero)

@[expose] def empty : RelativeRVFunctionRepresentative M S b D zero where
  count := 0
  object := Fin.elim0
  valid _ _ i := i.elim0

@[expose] def append : RelativeRVFunctionRepresentative M S b D zero where
  count := F.count + G.count
  object := Fin.addCases F.object G.object
  valid p hp := Fin.addCases (fun i => by simpa using F.valid p hp i) (fun j => by simpa using G.valid p hp j)

private theorem fiberObject_eq_of_scheme_eq
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0)) (p : D)
    {i : Fin F.count} {j : Fin G.count} (eq : F.object i = G.object j) :
    F.fiberObject hzero p i = G.fiberObject hzero p j := by
  have obj {W W' : RelativeRVObjectScheme M S (MixedVariables b Empty)} (e : W = W')
      (a : W.valid zero p.val) (b : W'.valid zero p.val) :
      (⟨W.data.degree,W.realize zero hzero p.val a⟩ : GradedObject M (M.termGenerated (namedTuple S p.val))) =
        ⟨W'.data.degree,W'.realize zero hzero p.val b⟩ := by
    subst W'
    rfl
  exact obj eq (F.valid p.val p.property i) (G.valid p.val p.property j)

private theorem totalLiftObject_eq_of_scheme_eq [TopologicalSpace (X .vf)]
    (d : SortedDefinableOver M S.carrier D) {i : Fin F.count} {j : Fin G.count} (eq : F.object i = G.object j) :
    F.totalLiftObject d i = G.totalLiftObject d j := by
  have obj {W W' : RelativeRVObjectScheme M S (MixedVariables b Empty)} (e : W = W')
      (a : ∀ p ∈ D, W.valid zero p) (b : ∀ p ∈ D, W'.valid zero p) :
      W.totalLiftObject d a = W'.totalLiftObject d b := by
    subst W'
    rfl
  exact obj eq (fun p hp => F.valid p hp i) (fun p hp => G.valid p hp j)

theorem fiberClass_append (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0)) (p : D) :
    (F.append G).fiberClass hzero p = F.fiberClass hzero p + G.fiberClass hzero p := by
  unfold fiberClass
  refine (Fin.sum_univ_add (fun i : Fin (F.count + G.count) =>
    objectClass M _ ((F.append G).fiberObject hzero p i))).trans ?_
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have eq : Fin.addCases F.object G.object (Fin.castAdd G.count i) = F.object i :=
      Fin.addCases_left (motive := fun _ => RelativeRVObjectScheme M S (MixedVariables b Empty)) i
    exact congrArg (objectClass M _) (fiberObject_eq_of_scheme_eq (F.append G) _ hzero p eq)
  · apply Finset.sum_congr rfl
    intro j _
    have eq : Fin.addCases F.object G.object (Fin.natAdd F.count j) = G.object j :=
      Fin.addCases_right (motive := fun _ => RelativeRVObjectScheme M S (MixedVariables b Empty)) j
    exact congrArg (objectClass M _) (fiberObject_eq_of_scheme_eq (F.append G) _ hzero p eq)

theorem totalLiftClass_append [TopologicalSpace (X .vf)]
    (d : SortedDefinableOver M S.carrier D) :
    (F.append G).totalLiftClass d = F.totalLiftClass d + G.totalLiftClass d := by
  unfold totalLiftClass
  refine (Fin.sum_univ_add (fun i : Fin (F.count + G.count) =>
    fieldClass M S ((F.append G).totalLiftObject d i))).trans ?_
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have eq : Fin.addCases F.object G.object (Fin.castAdd G.count i) = F.object i :=
      Fin.addCases_left (motive := fun _ => RelativeRVObjectScheme M S (MixedVariables b Empty)) i
    exact congrArg (fieldClass M S) (totalLiftObject_eq_of_scheme_eq (F.append G) _ d eq)
  · apply Finset.sum_congr rfl
    intro j _
    have eq : Fin.addCases F.object G.object (Fin.natAdd F.count j) = G.object j :=
      Fin.addCases_right (motive := fun _ => RelativeRVObjectScheme M S (MixedVariables b Empty)) j
    exact congrArg (fieldClass M S) (totalLiftObject_eq_of_scheme_eq (F.append G) _ d eq)

end RelativeRVFunctionRepresentative

section PositiveFunctions

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {b : ℕ}
  (D : Set (fieldAssignment b (CanonicalSort O)))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "P" => MixedVariables b Empty
local notation "R" => RelativeRVFunctionRepresentative 𝓜 S b D (baseRVZero S)

omit [TopologicalSpace K] in
theorem relativeFunctionFiberClass_append (F G : R) (p : D) :
    relativeFunctionFiberClass S neg D (F.append G) p =
      relativeFunctionFiberClass S neg D F p + relativeFunctionFiberClass S neg D G p := by
  unfold relativeFunctionFiberClass
  have eq := F.fiberClass_append G (by rfl) p
  apply Eq.trans (congrArg _ eq)
  exact map_add _ _ _

instance : Zero (RelativePositiveFunction S neg D) :=
  ⟨Quotient.mk _ (RelativeRVFunctionRepresentative.empty : R)⟩

instance : Add (RelativePositiveFunction S neg D) :=
  ⟨Quotient.map₂ RelativeRVFunctionRepresentative.append (by
    intro F F' h G G' g p
    exact (relativeFunctionFiberClass_append S neg D F G p).trans
      ((congrArg₂ (· + ·) (h p) (g p)).trans (relativeFunctionFiberClass_append S neg D F' G' p).symm))⟩

@[expose] def relativePositiveEval
    (f : RelativePositiveFunction S neg D) (p : D) :
    (gradedBlowupCongruence O hO power (relativeBase S p.val) (relativeBase_neg S neg p.val)).Quotient :=
  Quotient.liftOn f (fun F => relativeFunctionFiberClass S neg D F p) (fun _ _ eq => eq p)

omit [TopologicalSpace K] in
theorem relativePositiveEval_injective : Function.Injective (relativePositiveEval S neg D) := by
  intro f g h
  refine Quotient.inductionOn₂ f g (fun F G eq => Quotient.sound (fun p => congrFun eq p)) h

omit [TopologicalSpace K] in
theorem relativePositiveEval_zero (p : D) : relativePositiveEval S neg D 0 p = 0 := by
  change relativeFunctionFiberClass S neg D RelativeRVFunctionRepresentative.empty p = _
  unfold relativeFunctionFiberClass RelativeRVFunctionRepresentative.fiberClass RelativeRVFunctionRepresentative.empty
  simp only [Finset.univ_eq_empty,Finset.sum_empty]
  exact (gradedBlowupCongruence O hO power (relativeBase S p.val) (relativeBase_neg S neg p.val)).mk'.map_zero

omit [TopologicalSpace K] in
theorem relativePositiveEval_add (f g : RelativePositiveFunction S neg D) (p : D) :
    relativePositiveEval S neg D (f+g) p = relativePositiveEval S neg D f p + relativePositiveEval S neg D g p :=
  Quotient.inductionOn₂ f g (fun F G => relativeFunctionFiberClass_append S neg D F G p)

instance : AddCommMonoid (RelativePositiveFunction S neg D) where
  add_assoc f g h := relativePositiveEval_injective S neg D (funext fun p => by
    simp only [relativePositiveEval_add,add_assoc])
  zero_add f := relativePositiveEval_injective S neg D (funext fun p => by
    simp only [relativePositiveEval_add,relativePositiveEval_zero,zero_add])
  add_zero f := relativePositiveEval_injective S neg D (funext fun p => by
    simp only [relativePositiveEval_add,relativePositiveEval_zero,add_zero])
  add_comm f g := relativePositiveEval_injective S neg D (funext fun p => by
    simp only [relativePositiveEval_add,add_comm])
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

theorem relativePositiveIntegral_add
    (H : IntegrationHypotheses S neg)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (d : SortedDefinableOver 𝓜 S.carrier D)
    (fiber : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val))
    (f g : RelativePositiveFunction S neg D) :
    relativePositiveIntegral S neg D H sat d fiber (f+g) =
      relativePositiveIntegral S neg D H sat d fiber f + relativePositiveIntegral S neg D H sat d fiber g := by
  refine Quotient.inductionOn₂ f g (fun F G => ?_)
  change relativePositiveIntegral S neg D H sat d fiber (Quotient.mk _ (F.append G)) =
    relativePositiveIntegral S neg D H sat d fiber (Quotient.mk _ F) +
    relativePositiveIntegral S neg D H sat d fiber (Quotient.mk _ G)
  rw [relativePositiveIntegral_mk,relativePositiveIntegral_mk,relativePositiveIntegral_mk,
    RelativeRVFunctionRepresentative.totalLiftClass_append,map_add]

theorem relativePositiveIntegral_zero
    (H : IntegrationHypotheses S neg)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (d : SortedDefinableOver 𝓜 S.carrier D)
    (fiber : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val)) :
    relativePositiveIntegral S neg D H sat d fiber 0 = 0 := by
  change relativePositiveIntegral S neg D H sat d fiber
    (Quotient.mk _ (RelativeRVFunctionRepresentative.empty : R)) = _
  rw [relativePositiveIntegral_mk]
  unfold RelativeRVFunctionRepresentative.totalLiftClass RelativeRVFunctionRepresentative.empty
  simp

def relativePositiveIntegralHom
    (H : IntegrationHypotheses S neg)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (d : SortedDefinableOver 𝓜 S.carrier D)
    (fiber : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val)) :
    RelativePositiveFunction S neg D →+ (gradedBlowupCongruence O hO power S neg).Quotient where
  toFun := relativePositiveIntegral S neg D H sat d fiber
  map_zero' := relativePositiveIntegral_zero S neg D H sat d fiber
  map_add' := relativePositiveIntegral_add S neg D H sat d fiber

end PositiveFunctions

end GeneralizedEuler.Section5
