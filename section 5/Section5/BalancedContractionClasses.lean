module

public import Section5.DefinableCellTranslations
public import Section5.UnaryGradedClassComparison
public import Section5.ElementaryClassSteps
public import Section4.MultiplicativeDescent
import all Section4.DistinguishedResiduePoint
import all Section4.Objects

/-! In the two product forms of a balanced cell, the paradigm
contributes the same class on both sides. Mutual contraction of the
other factors therefore gives equality of the graded label classes. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cls" => objectClass 𝓜 S

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem opposite_paradigm_zero_iff (t : RV0 O) (u : RV O) :
    oppositeParadigm O t u = 0 ↔ t = 0 := by
  have neg : rv O (-1) ≠ 0 := (rv_eq_zero_iff O).not.mpr (neg_ne_zero.mpr one_ne_zero)
  have unit : (u : RV0 O) ≠ 0 := WithZero.coe_ne_zero
  have nonzeroInv : ((u : RV0 O)⁻¹) ≠ 0 := inv_ne_zero (G₀ := RV0 O) unit
  simp [oppositeParadigm,div_eq_mul_inv (G := RV0 O),neg,nonzeroInv]

/-- The zero paradigm contributes a degree-zero point. A named
nonzero paradigm contributes its singleton leading term in degree one. -/
def paradigmLabelObject (t : S.carrier .rv) : GradedObject 𝓜 S := by
  classical
  by_cases z : t.val = 0
  · exact ⟨0,degreeZeroUnit 𝓜 S⟩
  · let p : Fin 1 → RV0 O := fun _ => t.val
    have defP : isRVSet 𝓜 S ({p} : Set (Fin 1 → RV0 O)) :=
      oldTuple_definable (M := 𝓜) (S := S) p (fun _ => t.property)
    refine ⟨1,identityRVObject ({p} : Set (Fin 1 → RV0 O)) defP ?_⟩
    rintro _ rfl i
    exact z

open scoped Classical in
theorem paradigmLabelObject_class (t : S.carrier .rv) :
    cls (paradigmLabelObject O hO power S t) =
      if t.val = 0 then 1 else residuePointClass O hO power S := by
  classical
  unfold paradigmLabelObject
  split
  · exact degreeZeroUnit_class 𝓜 S
  · unfold residuePointClass
    apply scissors_sound 𝓜 S
    apply RVRelation.iso
    change RVDefinablyEquivalent 𝓜 S.carrier
      ({(fun _ : Fin 1 => t.val)} : Set (Fin 1 → RV0 O)) ({1} : Set (Fin 1 → RV0 O))
    exact singleton_equivalent (oldTuple_definable (M := 𝓜) (S := S) (fun _ : Fin 1 => t.val) (fun _ => t.property))
      (residuePointObject O hO power S).definable ⟨_,rfl⟩ ⟨1,rfl⟩
      (fun a => Subtype.ext a.property) (fun a => Subtype.ext a.property)

theorem balanced_paradigm_classes (t r : S.carrier .rv) (u : RV O)
    (rel : r.val = oppositeParadigm O t.val u) :
    cls (paradigmLabelObject O hO power S t) = cls (paradigmLabelObject O hO power S r) := by
  have e : r.val = 0 ↔ t.val = 0 := by rw [rel,opposite_paradigm_zero_iff]
  rw [paradigmLabelObject_class,paradigmLabelObject_class]
  by_cases ht : t.val = 0
  · simp only [ite_eq_left ht,ite_eq_left (e.2 ht)]
  · simp only [ite_eq_right ht,ite_eq_right (fun h => ht (e.1 h))]

variable {I J : Type} [Finite I] [Finite J] {m n : ℕ}
  {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}

theorem balanced_product_contraction_classes
    (idx : Fin m ≃ Fin 1 ⊕ I) (idy : Fin n ≃ Fin 1 ⊕ J)
    (defA : UnaryPullbackDefinable O hO power S A) (defB : UnaryPullbackDefinable O hO power S B)
    (fullA : IsUnaryPullback O A) (fullB : IsUnaryPullback O B)
    (finA : UnaryFiniteFibers A) (finB : UnaryFiniteFibers B)
    (f : A ≃ B) (graph : UnaryMixedGraphDefinable O hO power S f)
    (forward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) f)
    (backward : Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) f.symm)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (t r : S.carrier .rv) (u : RV O) (rel : r.val = oppositeParadigm O t.val u) :
    let a := unaryLabelObjects O hO power S A idx defA fullA finA
    let b := unaryLabelObjects O hO power S B idy defB fullB finB
    let T := paradigmLabelObject O hO power S t
    let R := paradigmLabelObject O hO power S r
    cls ⟨0+T.1,RVObject.cartesianProduct a.1 T.2⟩ + cls ⟨1+T.1,RVObject.cartesianProduct a.2 T.2⟩ =
      cls ⟨R.1+0,RVObject.cartesianProduct R.2 b.1⟩ + cls ⟨R.1+1,RVObject.cartesianProduct R.2 b.2⟩ := by
  intro a b T R
  obtain ⟨z,nz⟩ := unary_label_classes_of_mutual_contraction O hO power S idx idy defA defB
    fullA fullB finA finB f graph forward backward he small
  have paradigms : cls T = cls R := balanced_paradigm_classes O hO power S t r u rel
  change cls ⟨0,a.1⟩ = cls ⟨0,b.1⟩ at z
  change cls ⟨1,a.2⟩ = cls ⟨1,b.2⟩ at nz
  simp only [RVObject.cartesianProduct_class,z,nz,paradigms,mul_comm (cls R)]

end GeneralizedEuler.Section5
