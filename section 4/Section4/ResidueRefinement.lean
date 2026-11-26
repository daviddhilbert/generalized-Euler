module

public import Section4.MatrixPreimages
public import Section4.RefinementCoordinates
import all Section4.ResidueWeights
import all Section4.ResidueProducts
import all Section4.PositivePresentations
import all Section4.Objects
import all Section4.DefinableResidueMatrices

/-! The rank-loss identity inside the actual residue Grothendieck semiring. -/
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
  {G : Submodule F (Additive O.ValueGroupˣ)} {r k n m : ℕ}
  (A : ValueFrame G r n) (B : ValueFrame G k n)

local instance refinementKernelGroup : AddCommGroup v.ker := @Submodule.addCommGroup F (Additive (PositiveRV O)) _ _ _ v.ker
local instance refinementKernelModule : Module F v.ker := @Submodule.module F (Additive (PositiveRV O)) _ _ _ v.ker

include powers in
theorem residue_refinement_class (iA : Fin m ≃ A.dependent) (iB : Fin (m + (r-k)) ≃ B.dependent)
    (α : Fin k → Additive O.ValueGroupˣ) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) (D : Set (A.dependent → v.ker)) (hd : isRVSet _ S (unitSet O v iA D)) :
    let R := {b : B.dependent → v.ker | A.residuePart (B.padResidue b) ∈ D}
    ∃ hR : isRVSet _ S (unitSet O v iB R),
      unitWeight O v hv hO P S iB R hR =
        unitWeight O v hv hO P S iA D hd * entireUnitWeight O v hv hO P S 1 ^ (r-k) := by
  classical
  obtain ⟨L,N,coeff,bij,image⟩ := A.refinement_coordinates (T := v.ker) B iA α hi h
  let R := actRows L ⁻¹' D
  have orig : {b : B.dependent → v.ker | A.residuePart (B.padResidue b) ∈ D} = R :=
    Set.ext fun b => (congrArg (· ∈ D) (coeff b)).to_iff.symm
  dsimp only
  rw [orig]
  have hR := unit_matrix_preimage O v hv hO P powers S iB iA L D hd
  refine ⟨hR,?_⟩
  let idc := Equiv.refl (Fin (r-k))
  let packed := packedProduct O v iA idc D Set.univ
  have heq : actRows N '' R = packed := by
    rw [image D]
    ext y; exact ⟨fun h => ⟨h,Set.mem_univ _⟩,And.left⟩
  have e := unit_matrix_equivalence O v iB (Equiv.refl _) N P powers hO S R hR bij.1.injOn
  rw [heq] at e
  obtain ⟨hp,mul⟩ := unit_product O v hv hO P S iA idc D Set.univ hd (unit_univ_definable O v hv hO P S idc)
  have same : unitWeight O v hv hO P S iB R hR = unitWeight O v hv hO P S (Equiv.refl _) packed hp :=
    residue_class_iso _ _ _ _ e
  exact (same.trans mul).trans (congrArg (unitWeight O v hv hO P S iA D hd * ·)
    (entireUnitWeight_power O v hv hO P S (r-k)))

end GeneralizedEuler.Section4
