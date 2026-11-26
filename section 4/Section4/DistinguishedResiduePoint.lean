module

public import Section4.PositivePresentations
public import Section4.RVParameterSlices
public import Section4.ResidueScissors
import all Section4.PositivePresentations
import all Section4.Objects
import all Section2.SortedStructure

/-! The residue singleton with identity label in degree one. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
set_option backward.isDefEq.respectTransparency false
open FirstOrder GeneralizedEuler.Section2
variable {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {J : Language} [J.Structure K] (O : ValuationSubring K) [J.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
local notation "M" => canonicalStructure (L := J) O hO P

def residuePointObject : RVObject M S 1 :=
  identityRVObject ({1} : Set (Fin 1 → RV0 O))
    (oldTuple_definable _ (fun _ => S.closed .rvOne (fun i => i.elim0) (fun i => i.elim0)))
    (by rintro _ rfl j; change (1 : RV0 O) ≠ 0; simpa only [map_one] using (rv_eq_zero_iff O).not.mpr (one_ne_zero : (1 : K) ≠ 0))

theorem residuePoint_finite {Γ : Type*} (v : RV0 O → Γ) : (residuePointObject O hO P S).IsResidue M S v := by
  unfold RVObject.IsResidue
  apply Set.Finite.subset (Set.finite_singleton (v ∘ (1 : Fin 1 → RV0 O)))
  rintro _ ⟨x,rfl⟩
  exact congrArg (v ∘ ·) (show x.val=(1 : Fin 1 → RV0 O) from x.property)

end GeneralizedEuler.Section4
