module

public import Section4.ResidueWeights
public import Section4.ResidueMatrices
import all Section4.ResidueWeights
import all Section4.DefinableResidueMatrices
import all Section4.RectangleClasses
import all Section4.PositivePresentations
import all Section4.Objects
import all Section4.ResidueScissors
import all Section4.ResidueMatrices

/-! Re-indexing a positive unit tuple preserves its homogeneous residue
class for arbitrary enumerations of the source and target coordinates. -/
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

local instance reindexKernelGroup : AddCommGroup v.ker := @Submodule.addCommGroup F (Additive (PositiveRV O)) _ _ _ v.ker
local instance reindexKernelModule : Module F v.ker := @Submodule.module F (Additive (PositiveRV O)) _ _ _ v.ker

include powers in
theorem reindex_unit_class {I H : Type} [Fintype I] {m n} (idx : Fin m ≃ I) (idy : Fin n ≃ H)
    (p : H ≃ I) (B : Set (I → v.ker)) (hb : isRVSet _ S (unitSet O v idx B)) :
    let R := {y : H → v.ker | y ∘ p.symm ∈ B}
    ∃ hR : isRVSet _ S (unitSet O v idy R), unitWeight O v hv hO P S idy R hR = unitWeight O v hv hO P S idx B hb := by
  let e := idx.trans (p.symm.trans idy.symm)
  have dim : m = n := Fin.equiv_iff_eq.mp ⟨e⟩
  subst n
  let R := {y : H → v.ker | y ∘ p.symm ∈ B}
  let A := readMatrix (F := F) p
  have image : actRows (T := v.ker) A '' B = R := by
    ext y; constructor
    · rintro ⟨x,hx,rfl⟩
      change actRows A x ∘ p.symm ∈ B
      rw [act_read]; simpa [Function.comp_def] using hx
    · intro hy; exact ⟨y ∘ p.symm,hy,(act_read p _).trans (funext (fun j => congrArg y (p.symm_apply_apply j)))⟩
  have inj : Function.Injective (actRows (T := v.ker) A) := by
    intro x y eq; rw [act_read,act_read] at eq
    exact p.surjective.right_cancellable.mp eq
  have iso := unit_matrix_equivalence O v idx idy A P powers hO S B hb inj.injOn
  rw [image] at iso
  dsimp only
  refine ⟨rv_equivalent_target_definable iso,?_⟩
  symm; exact residue_class_iso _ _ _ _ iso

end GeneralizedEuler.Section4
