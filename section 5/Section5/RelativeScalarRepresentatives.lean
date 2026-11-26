module

public import Section5.RelativeIntegralAddition
public import Section5.RelativeRVProducts
public import Section5.ConstantRelativeRVObjects

/-! A constant RV object acts on a relative representative by taking
its Cartesian product with each tagged object. Fiber classes multiply
after extending the coefficient to the generated base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

namespace RelativeRVFunctionRepresentative

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {b k : ℕ}
  {D : Set (fieldAssignment b X)} {zero : S.carrier .rv}
  (F : RelativeRVFunctionRepresentative M S b D zero)
  (C : RelativeRVObjectScheme M S (MixedVariables b Empty))
  (valid : ∀ p ∈ D, C.valid zero p)

@[expose] def productWith : RelativeRVFunctionRepresentative M S b D zero where
  count := F.count
  object i := (F.object i).cartesianProduct C
  valid p hp i := (F.object i).cartesianProduct_valid C (F.valid p hp i) (valid p hp)

theorem fiberClass_productWith (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0)) (p : D) :
    let T := M.termGenerated (namedTuple S p.val)
    (F.productWith C valid).fiberClass hzero p =
      F.fiberClass hzero p * objectClass M T ⟨C.data.degree,C.realize zero hzero p.val (valid p.val p.property)⟩ := by
  intro T
  unfold fiberClass
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => (F.object i).cartesianProduct_realize_class C hzero
    (F.valid p.val p.property i) (valid p.val p.property))

end RelativeRVFunctionRepresentative

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {b : ℕ}
  (D : Set (fieldAssignment b (CanonicalSort O)))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Q" => (gradedBlowupCongruence O hO power S neg)
local notation "R" => RelativeRVFunctionRepresentative 𝓜 S b D (baseRVZero S)
local notation "Qp" p => (gradedBlowupCongruence O hO power (relativeBase S (Subtype.val p))
  (relativeBase_neg S neg (Subtype.val p)))

def relativeCoefficient (H : IntegrationHypotheses S neg) (p : D)
    (Hp : IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val)) :
    (Q).Quotient →+* (Qp p).Quotient :=
  let base := fieldClassBaseExtension (M := 𝓜) (base_subset_named (S := S) p.val)
  (positiveLiftEquiv _ _ Hp).symm.toRingHom.comp (base.comp (positiveLiftEquiv S neg H).toRingHom)

theorem relativeFunctionFiberClass_productWith_constant
    (H : IntegrationHypotheses S neg) (p : D)
    (Hp : IntegrationHypotheses (relativeBase S p.val) (relativeBase_neg S neg p.val))
    (F : R) (U : GradedObject 𝓜 S) (bound : ℕ)
    (valid : ∀ p ∈ D, (constantRelativeRVObject U.2 bound).valid (baseRVZero S) p) :
    relativeFunctionFiberClass S neg D (F.productWith (constantRelativeRVObject U.2 bound) valid) p =
      relativeCoefficient S neg D H p Hp ((Q).mk' (objectClass 𝓜 S U)) *
        relativeFunctionFiberClass S neg D F p := by
  let T := relativeBase S p.val
  let nt := relativeBase_neg S neg p.val
  let C := constantRelativeRVObject (P := MixedVariables b Empty) U.2 bound
  let W := C.realize (baseRVZero S) (by rfl) p.val (valid p.val p.property)
  let e := positiveLiftEquiv T nt Hp
  let a := ((Q).mk') (objectClass 𝓜 S U)
  let cf := relativeCoefficient S neg D H p Hp
  have coeff : e (cf a) = liftObjectClass ⟨U.1,W⟩ := by
    change e (e.symm (fieldClassBaseExtension (M := 𝓜) (base_subset_named (S := S) p.val)
      (positiveLiftEquiv S neg H a))) = _
    refine (e.apply_symm_apply (fieldClassBaseExtension (M := 𝓜)
      (base_subset_named (S := S) p.val) (positiveLiftEquiv S neg H a))).trans ?_
    exact (congrArg (fieldClassBaseExtension (M := 𝓜) (base_subset_named (S := S) p.val))
      (positiveLiftEquiv_mk S neg H (objectClass 𝓜 S U))).trans
      ((congrArg (fieldClassBaseExtension (M := 𝓜) (base_subset_named (S := S) p.val))
        (liftClassHom_class H.liftIso U)).trans
        (constantRelativeRVObject_lift_class U.2 bound p.val (baseRVZero S) rfl (valid p.val p.property)).symm)
  apply e.injective
  have product := F.fiberClass_productWith C valid (by rfl) p
  have qproduct : relativeFunctionFiberClass S neg D (F.productWith C valid) p =
      relativeFunctionFiberClass S neg D F p *
        (gradedBlowupCongruence O hO power T nt).mk' (objectClass 𝓜 T ⟨U.1,W⟩) := by
    exact (congrArg ((gradedBlowupCongruence O hO power T nt).mk') product).trans (map_mul _ _ _)
  change e (relativeFunctionFiberClass S neg D (F.productWith C valid) p) =
    e (cf a * relativeFunctionFiberClass S neg D F p)
  rw [qproduct,map_mul,map_mul,coeff]
  have value := (positiveLiftEquiv_mk T nt Hp (objectClass 𝓜 T ⟨U.1,W⟩)).trans
    (liftClassHom_class Hp.liftIso ⟨U.1,W⟩)
  exact (congrArg (fun y => e (relativeFunctionFiberClass S neg D F p) * y) value).trans (mul_comm _ _)

end GeneralizedEuler.Section5
