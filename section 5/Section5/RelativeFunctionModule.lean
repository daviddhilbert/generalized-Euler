module

public import Section5.RelativeScalarRepresentatives
public import Mathlib.Algebra.Module.Defs

/-! Pointwise multiplication by a constant RV class has a relative
representative. The evaluation maps detect equality and verify the
semimodule laws. -/

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
local notation "Q" => (gradedBlowupCongruence O hO power S neg)
local notation "F" => RelativePositiveFunction S neg D
local notation "Qp" p => (gradedBlowupCongruence O hO power (relativeBase S (Subtype.val p))
  (relativeBase_neg S neg (Subtype.val p)))

def relativePositiveEvalHom (p : D) : F →+ (Qp p).Quotient where
  toFun f := relativePositiveEval S neg D f p
  map_zero' := relativePositiveEval_zero S neg D p
  map_add' f g := relativePositiveEval_add S neg D f g p

variable (H : IntegrationHypotheses S neg)
  (fibers : ∀ p : D, IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val))
  (sat : ∀ k, RealizesFinitelySatisfiableTypes (canonicalStructure (L := L) O hO power)
    (WithBase S.carrier (RVVariables (Fin k))) (BaseAssignments S.carrier (RVVariables (Fin k))))

include sat

theorem exists_constant_class_multiple (U : GradedObject 𝓜 S) (f : F) :
    ∃ g : F, ∀ p : D, relativePositiveEval S neg D g p =
      relativeCoefficient S neg D H p (fibers p) ((Q).mk' (objectClass 𝓜 S U)) *
        relativePositiveEval S neg D f p := by
  refine Quotient.inductionOn f (fun A => ?_)
  obtain ⟨bound,finite⟩ := rvObject_uniform_label_bound U.2 (sat U.1)
  let C := constantRelativeRVObject (P := MixedVariables b Empty) U.2 bound
  have valid : ∀ p ∈ D, C.valid (baseRVZero S) p :=
    fun p _ => constantRelativeRVObject_valid U.2 bound p (baseRVZero S) rfl finite
  exact ⟨Quotient.mk _ (A.productWith C valid),fun p =>
    relativeFunctionFiberClass_productWith_constant S neg D H p (fibers p) A U bound valid⟩

theorem exists_relative_scalar_multiple (a : (Q).Quotient) (f : F) :
    ∃ g : F, ∀ p : D, relativePositiveEval S neg D g p =
      relativeCoefficient S neg D H p (fibers p) a * relativePositiveEval S neg D f p := by
  classical
  obtain ⟨r,hr⟩ := (Q).mk'_surjective a
  obtain ⟨k,U,eq⟩ := positive_class_represented 𝓜 S r
  have h (i : Fin k) := exists_constant_class_multiple S neg D H fibers sat (U i) f
  choose g hg using h
  refine ⟨∑ i, g i,fun p => ?_⟩
  let e := relativePositiveEvalHom S neg D p
  let q := (relativeCoefficient S neg D H p (fibers p)).comp ((Q).mk')
  let v := relativePositiveEval S neg D f p
  change e (∑ i, g i) = relativeCoefficient S neg D H p (fibers p) a * v
  have sumImage := map_sum q (fun i => objectClass 𝓜 S (U i)) Finset.univ
  have coefficient : relativeCoefficient S neg D H p (fibers p) a =
      ∑ i, q (objectClass 𝓜 S (U i)) :=
    (congrArg (relativeCoefficient S neg D H p (fibers p)) hr).symm.trans
      ((congrArg q eq).trans sumImage)
  calc
    _ = ∑ i, e (g i) := map_sum e g Finset.univ
    _ = ∑ i, q (objectClass 𝓜 S (U i)) * v := Finset.sum_congr rfl (fun i _ => hg i p)
    _ = (∑ i, q (objectClass 𝓜 S (U i))) * v := (Finset.sum_mul _ _ _).symm
    _ = _ := congrArg (· * v) coefficient.symm

def relativeScalarMultiple (a : (Q).Quotient) (f : F) : F :=
  (exists_relative_scalar_multiple S neg D H fibers sat a f).choose

theorem relativePositiveEval_scalarMultiple (a : (Q).Quotient) (f : F) (p : D) :
    relativePositiveEval S neg D (relativeScalarMultiple S neg D H fibers sat a f) p =
      relativeCoefficient S neg D H p (fibers p) a * relativePositiveEval S neg D f p :=
  (exists_relative_scalar_multiple S neg D H fibers sat a f).choose_spec p

@[expose, instance_reducible] def relativePositiveModule : Module (Q).Quotient F := by
  let act := relativeScalarMultiple S neg D H fibers sat
  have ev (a : (Q).Quotient) (f : F) (p : D) :
      relativePositiveEval S neg D (act a f) p =
        relativeCoefficient S neg D H p (fibers p) a * relativePositiveEval S neg D f p :=
    relativePositiveEval_scalarMultiple S neg D H fibers sat a f p
  have one (f : F) : act 1 f = f := relativePositiveEval_injective S neg D (funext fun p => by
    rw [ev,map_one,one_mul])
  have mul (a b : (Q).Quotient) (f : F) : act (a*b) f = act a (act b f) :=
    relativePositiveEval_injective S neg D (funext fun p => by rw [ev,ev,ev,map_mul,mul_assoc])
  have az (a : (Q).Quotient) : act a 0 = 0 := relativePositiveEval_injective S neg D (funext fun p => by
    rw [ev,relativePositiveEval_zero,mul_zero])
  have af (a : (Q).Quotient) (f g : F) : act a (f+g) = act a f + act a g :=
    relativePositiveEval_injective S neg D (funext fun p => by
      rw [ev,relativePositiveEval_add,relativePositiveEval_add,ev,ev,mul_add])
  have ad (a b : (Q).Quotient) (f : F) : act (a+b) f = act a f + act b f :=
    relativePositiveEval_injective S neg D (funext fun p => by
      rw [ev,map_add,relativePositiveEval_add,ev,ev,add_mul])
  have za (f : F) : act 0 f = 0 := relativePositiveEval_injective S neg D (funext fun p => by
    rw [ev,map_zero,zero_mul,relativePositiveEval_zero])
  exact
    { smul := act
      one_smul := one
      mul_smul := mul
      smul_zero := az
      smul_add := af
      add_smul := ad
      zero_smul := za }

end GeneralizedEuler.Section5
