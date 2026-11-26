module

public import Section4.ProjectedResidues
public import Section4.SliceWeights
import all Section4.ResidueWeights
import all Section4.DefinableResidueMatrices
import all Section4.ProjectedResidues
import all Section4.RectangleClasses
import all Section4.SliceWeights
import all Section4.ResidueScissors

/-! Comparing projected residue classes in their common target degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {G : Submodule F (Additive O.ValueGroupˣ)} {r k n : ℕ} {A : ValueFrame G r n}

local instance projKernelGroup : AddCommGroup v.ker := @Submodule.addCommGroup F (Additive (PositiveRV O)) _ _ _ v.ker
local instance projKernelModule : Module F v.ker := @Submodule.module F (Additive (PositiveRV O)) _ _ _ v.ker

namespace ProjectionBasis
variable {p : Fin k → Fin n} (q : ProjectionBasis A p)

include powers in
theorem projected_residue_equivalence (D : Set (A.dependent → v.ker))
    (hd : isRVSet _ S (unitSet O v (residueIndex A) D)) (inj : Set.InjOn ((projectResidues (T := Additive (PositiveRV O)) v q)) D) :
    RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (unitSet O v (residueIndex A) D)
      (unitSet O v (residueIndex q.frame) ((projectResidues (T := Additive (PositiveRV O)) v q) '' D)) := by
  have eq : (projectResidues (T := Additive (PositiveRV O)) v q) = actRows q.projectionMatrix := funext (projectResidues_eq (T := Additive (PositiveRV O)) v q)
  rw [eq] at inj ⊢
  exact unit_matrix_equivalence O v (residueIndex A) (residueIndex q.frame) q.projectionMatrix P powers hO S D hd inj

include powers in
theorem projected_residue_class {p' : Fin k → Fin n} (q' : ProjectionBasis A p')
    (D : Set (A.dependent → v.ker)) (hd : isRVSet _ S (unitSet O v (residueIndex A) D))
    (inj : Set.InjOn ((projectResidues (T := Additive (PositiveRV O)) v q)) D) (inj' : Set.InjOn ((projectResidues (T := Additive (PositiveRV O)) v q')) D) :
    ∃ (h : isRVSet _ S (unitSet O v (residueIndex q.frame) ((projectResidues (T := Additive (PositiveRV O)) v q) '' D)))
      (h' : isRVSet _ S (unitSet O v (residueIndex q'.frame) ((projectResidues (T := Additive (PositiveRV O)) v q') '' D))),
      unitWeight O v hv hO P S (residueIndex q.frame) ((projectResidues (T := Additive (PositiveRV O)) v q) '' D) h =
        unitWeight O v hv hO P S (residueIndex q'.frame) ((projectResidues (T := Additive (PositiveRV O)) v q') '' D) h' := by
  have left := q.projected_residue_equivalence O v hO P powers S D hd inj
  have right := q'.projected_residue_equivalence O v hO P powers S D hd inj'
  refine ⟨rv_equivalent_target_definable left,rv_equivalent_target_definable right,?_⟩
  exact residue_class_iso _ _ _ _ (left.symm.trans right)

end ProjectionBasis
end GeneralizedEuler.Section4
