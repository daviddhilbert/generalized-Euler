module

public import Section5.RelativeFunctionModule
public import Section5.RelativeConstantLiftProducts
public import Mathlib.Algebra.Module.LinearMap.Defs

/-! Positive relative integration is linear over the fixed-base
RV quotient. The scalar law follows from the total-lift product. -/

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
  (D : Set (fieldAssignment b (CanonicalSort O)))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "ParamVars" => MixedVariables b Empty
local notation "Q" => (gradedBlowupCongruence O hO power S neg)
local notation "F" => RelativePositiveFunction S neg D
local notation "Rep" => RelativeRVFunctionRepresentative 𝓜 S b D (baseRVZero S)

variable (H : IntegrationHypotheses S neg)
  (fiber : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val))
  (satRV : ∀ k, RealizesFinitelySatisfiableTypes (canonicalStructure (L := L) O hO power)
    (WithBase S.carrier (RVVariables (Fin k))) (BaseAssignments S.carrier (RVVariables (Fin k))))

local notation "satP" => RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier ParamVars) (BaseAssignments S.carrier ParamVars)

theorem relativePositiveIntegral_generator_scalar
    (sat : satP) (d : SortedDefinableOver 𝓜 S.carrier D) (U : GradedObject 𝓜 S) (f : F) :
    relativePositiveIntegral S neg D H sat d fiber
      (relativeScalarMultiple S neg D H fiber satRV ((Q).mk' (objectClass 𝓜 S U)) f) =
      ((Q).mk' (objectClass 𝓜 S U)) * relativePositiveIntegral S neg D H sat d fiber f := by
  refine Quotient.inductionOn f (fun A => ?_)
  let a := ((Q).mk') (objectClass 𝓜 S U)
  obtain ⟨bound,finite⟩ := rvObject_uniform_label_bound U.2 (satRV U.1)
  let C := constantRelativeRVObject (P := ParamVars) U.2 bound
  have valid : ∀ p ∈ D, C.valid (baseRVZero S) p :=
    fun p _ => constantRelativeRVObject_valid U.2 bound p (baseRVZero S) rfl finite
  let B := A.productWith C valid
  have h : relativeScalarMultiple S neg D H fiber satRV a (Quotient.mk _ A) = Quotient.mk _ B := by
    apply relativePositiveEval_injective S neg D
    funext p
    exact (relativePositiveEval_scalarMultiple S neg D H fiber satRV a (Quotient.mk _ A) p).trans
      ((relativeFunctionFiberClass_productWith_constant S neg D H p (fiber p) A U bound valid).symm)
  change relativePositiveIntegral S neg D H sat d fiber
    (relativeScalarMultiple S neg D H fiber satRV a (Quotient.mk _ A)) =
      a * relativePositiveIntegral S neg D H sat d fiber (Quotient.mk _ A)
  rw [h,relativePositiveIntegral_mk,relativePositiveIntegral_mk]
  have product : B.totalLiftClass d = A.totalLiftClass d * liftObjectClass U := by
    unfold RelativeRVFunctionRepresentative.totalLiftClass
    calc
      _ = ∑ i : Fin A.count, fieldClass 𝓜 S (A.totalLiftObject d i) * liftObjectClass U :=
        Finset.sum_congr rfl (fun i _ => totalLiftObject_product_with_constant
          (A.object i) U.2 bound d (fun p hp => A.valid p hp i) valid)
      _ = _ := (Finset.sum_mul _ _ _).symm
  let e := (positiveLiftEquiv S neg H).symm
  have coeff : e (liftObjectClass U) = a :=
    (congrArg e (liftClassHom_class H.liftIso U)).symm.trans (positiveIntegral_lift S neg H (objectClass 𝓜 S U))
  have commute : e (A.totalLiftClass d) * a = a * e (A.totalLiftClass d) :=
    mul_comm (e (A.totalLiftClass d)) a
  exact (congrArg e product).trans ((map_mul e _ _).trans
    ((congrArg (fun a => e (A.totalLiftClass d) * a) coeff).trans commute))

theorem relativePositiveIntegral_scalar
    (sat : satP) (d : SortedDefinableOver 𝓜 S.carrier D) (a : (Q).Quotient) (f : F) :
    relativePositiveIntegral S neg D H sat d fiber (relativeScalarMultiple S neg D H fiber satRV a f) =
      a * relativePositiveIntegral S neg D H sat d fiber f := by
  classical
  let act := relativeScalarMultiple S neg D H fiber satRV
  let int := relativePositiveIntegral S neg D H sat d fiber
  have eval (a : (Q).Quotient) (p : D) : relativePositiveEval S neg D (act a f) p =
      relativeCoefficient S neg D H p (fiber p) a * relativePositiveEval S neg D f p :=
    relativePositiveEval_scalarMultiple S neg D H fiber satRV a f p
  have zero : act 0 f = 0 := relativePositiveEval_injective S neg D (funext fun p => by
    rw [eval,map_zero,zero_mul,relativePositiveEval_zero])
  have add (a b : (Q).Quotient) : act (a+b) f = act a f + act b f :=
    relativePositiveEval_injective S neg D (funext fun p => by
      rw [eval,map_add,relativePositiveEval_add,eval,eval,add_mul])
  let L : AddSubmonoid (Q).Quotient :=
    { carrier := {a | int (act a f) = a * int f}
      zero_mem' := by
        change int (act 0 f) = 0 * int f
        exact (congrArg int zero).trans
          ((relativePositiveIntegral_zero S neg D H sat d fiber).trans (zero_mul _).symm)
      add_mem' := by
        intro a b ha hb
        change int (act a f) = a * int f at ha
        change int (act b f) = b * int f at hb
        change int (act (a+b) f) = (a+b) * int f
        exact (congrArg int (add a b)).trans
          ((relativePositiveIntegral_add S neg D H sat d fiber (act a f) (act b f)).trans
            ((congrArg₂ (· + ·) ha hb).trans (add_mul _ _ _).symm)) }
  have gen (U : GradedObject 𝓜 S) : ((Q).mk') (objectClass 𝓜 S U) ∈ L :=
    relativePositiveIntegral_generator_scalar S neg D H fiber satRV sat d U f
  obtain ⟨r,hr⟩ := (Q).mk'_surjective a
  obtain ⟨k,U,eq⟩ := positive_class_represented 𝓜 S r
  have ea : a = ∑ i, ((Q).mk') (objectClass 𝓜 S (U i)) := hr.symm.trans
    ((congrArg ((Q).mk') eq).trans (map_sum ((Q).mk') (fun i => objectClass 𝓜 S (U i)) Finset.univ))
  have asMem : a ∈ L := ea.symm ▸ AddSubmonoid.sum_mem L (fun i _ => gen (U i))
  exact asMem

def relativePositiveLinearIntegral (sat : satP) (d : SortedDefinableOver 𝓜 S.carrier D) :
    letI := relativePositiveModule S neg D H fiber satRV
    F →ₗ[(Q).Quotient] (Q).Quotient :=
  letI := relativePositiveModule S neg D H fiber satRV
  { toFun := relativePositiveIntegral S neg D H sat d fiber
    map_add' := relativePositiveIntegral_add S neg D H sat d fiber
    map_smul' := by
      intro a f
      change relativePositiveIntegral S neg D H sat d fiber (relativeScalarMultiple S neg D H fiber satRV a f) =
        a * relativePositiveIntegral S neg D H sat d fiber f
      exact relativePositiveIntegral_scalar S neg D H fiber satRV sat d a f }

end GeneralizedEuler.Section5
