module

public import Section5.UnitLabelExtension
public import Section5.PositiveRVClasses
public import Section5.BlowupIteration

/-! One elementary blowup on the positive scissor classes. A witness
specifies an actual lower-degree RV object for the center. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (hneg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cls" => objectClass 𝓜 S

@[expose] def residuePointClass : RVSemiring 𝓜 S := cls ⟨1,residuePointObject O hO power S⟩

@[expose] def multiplierClass : RVSemiring 𝓜 S := cls ⟨1,multiplierObject O hO power S hneg⟩

local notation "p" => residuePointClass O hO power S
local notation "q" => multiplierClass O hO power S hneg

/-- The untouched parts of the graded object stay in the same class.
The class of the center has its degree increased by a point on entry.
It has two strata on exit, with the nonzero multipliers in the old
degree and the zero multiplier in the lower degree. -/
@[expose] def ElementaryClassStep (a b : RVSemiring 𝓜 S) : Prop :=
  a = b ∨ ∃ (W : GradedObject 𝓜 S) (rest : RVSemiring 𝓜 S),
    a = cls W * p + rest ∧ b = cls W * (1 + q) + rest

theorem elementaryClassStep_add {a b : RVSemiring 𝓜 S}
    (h : ElementaryClassStep O hO power S hneg a b) (c : RVSemiring 𝓜 S) :
    ElementaryClassStep O hO power S hneg (a+c) (b+c) := by
  rcases h with e | ⟨W,rest,ha,hb⟩
  · exact Or.inl (congrArg (· + c) e)
  · exact Or.inr ⟨W,rest+c,by rw [ha,add_assoc],by rw [hb,add_assoc]⟩

theorem elementaryClassStep_of_blowup {k m : ℕ}
    (U : RVObject 𝓜 S (k+1)) (j : Fin (k+1)) (idx : Fin m ≃ Fin U.arity ⊕ Fin 1)
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite)
    (rest : RVSemiring 𝓜 S) :
    ElementaryClassStep O hO power S hneg (cls ⟨k+1,U⟩ + rest)
      (cls ⟨k,zeroBlowupObject U j finiteDelete⟩ +
        cls ⟨k+1,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ + rest) := by
  refine Or.inr ⟨⟨k,zeroBlowupObject U j finiteDelete⟩,rest,?_,?_⟩
  · rw [blowup_original_class_factor O hO power S U j finiteDelete,residuePointClass]
  · rw [positiveBlowup_class_factor O hO power S U idx hneg j finiteDelete,mul_add,mul_one,multiplierClass]

/-- Conversely the class formula is realized by an elementary blowup
of the presentation obtained by appending a unit coordinate. -/
theorem elementaryClassStep_center_realization (W : GradedObject 𝓜 S) :
    let nz := canonical_rvUnit_nonzero (L := L) O hO power
    let U := appendUnitLabel W.2 nz
    let j := Fin.last W.1
    let finiteDelete := appendUnitLabel_finite_deletion W.2 nz
    let idx : Fin (U.arity+1) ≃ Fin U.arity ⊕ Fin 1 := finSumFinEquiv.symm
    cls ⟨W.1+1,U⟩ = cls W * p ∧
      cls ⟨W.1,zeroBlowupObject U j finiteDelete⟩ +
        cls ⟨W.1+1,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ = cls W * (1 + q) := by
  intro nz U j finiteDelete idx
  refine ⟨appendUnitLabel_class O hO power S W.2,?_⟩
  rw [positiveBlowup_class_factor O hO power S U idx hneg j finiteDelete,
    appendUnitLabel_zero_class W.2 nz,mul_add,mul_one,multiplierClass]

theorem elementaryClassStep_mul_object {a b : RVSemiring 𝓜 S}
    (h : ElementaryClassStep O hO power S hneg a b) (V : GradedObject 𝓜 S) :
    ElementaryClassStep O hO power S hneg (a*cls V) (b*cls V) := by
  rcases h with e | ⟨W,rest,ha,hb⟩
  · exact Or.inl (congrArg (· * cls V) e)
  · let T : GradedObject 𝓜 S := ⟨W.1+V.1,RVObject.cartesianProduct W.2 V.2⟩
    have ht : cls T = cls W * cls V := RVObject.cartesianProduct_class _ _
    exact Or.inr ⟨T,rest * cls V,
      by rw [ha,add_mul,ht,mul_right_comm],
      by rw [hb,add_mul,ht,mul_right_comm]⟩

end GeneralizedEuler.Section5
