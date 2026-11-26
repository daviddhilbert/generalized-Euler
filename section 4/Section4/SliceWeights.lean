module

public import Section4.ResidueRefinement
public import Section4.SliceComparison
public import Section4.ValueSubdivisionSum
import all Section4.ResidueWeights
import all Section4.SliceComparison
import all Section4.PositiveRectangles

/-! The two fixed-base scissor identities needed to compare positive chart weights. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false

def residueIndex {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {G : Submodule F V}
    {n r : ℕ} (A : ValueFrame G r n) : Fin (n-r) ≃ A.dependent :=
  (Fintype.equivFinOfCardEq (complement_count A.free)).symm

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] {G : Submodule F (Additive O.ValueGroupˣ)} {n : ℕ}
  (p : ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n) (c : DefinablePiece JG G n)

def ChartPiece.measurable := isRVSet _ S (unitSet O v (residueIndex p.value.frame) p.residue)

def ChartPiece.residueWeight (h : p.measurable O v hO P S) :=
  unitWeight O v hv hO P S (residueIndex p.value.frame) p.residue h

local instance sliceKernelGroup : AddCommGroup v.ker := @Submodule.addCommGroup F (Additive (PositiveRV O)) _ _ _ v.ker
local instance sliceKernelModule : Module F v.ker := @Submodule.module F (Additive (PositiveRV O)) _ _ _ v.ker

include powers in
theorem frame_slice_weight {r l} (A : ValueFrame G r n) (B : ValueFrame G l n)
    (R : Set (A.dependent → v.ker)) (hR : isRVSet _ S (unitSet O v (residueIndex A) R))
    (α : Fin l → Additive O.ValueGroupˣ) (hi : LinearIndependent F (G.mkQ ∘ α)) (hit : B.eval α ∈ Set.range A.eval) :
    let res := {b : B.dependent → v.ker | A.residuePart (B.padResidue b) ∈ R}
    ∃ h : isRVSet _ S (unitSet O v (residueIndex B) res),
      unitWeight O v hv hO P S (residueIndex B) res h =
        unitWeight O v hv hO P S (residueIndex A) R hR * entireUnitWeight O v hv hO P S 1 ^ (r-l) := by
  dsimp only
  let res := {b : B.dependent → v.ker | A.residuePart (B.padResidue b) ∈ R}
  have le := A.refinement_rank B α hi hit
  have bound := Fintype.card_le_of_injective A.free A.free.injective
  simp only [Fintype.card_fin] at bound
  have dims : n - r + (r - l) = n - l := by omega
  have step {m} (idx : Fin m ≃ B.dependent) (dim : n-r + (r-l) = m) :
      ∃ h : isRVSet _ S (unitSet O v idx res),
        unitWeight O v hv hO P S idx res h =
          unitWeight O v hv hO P S (residueIndex A) R hR * entireUnitWeight O v hv hO P S 1 ^ (r - l) := by
    subst m
    exact residue_refinement_class O v hv hO P powers S A B (residueIndex _) idx α hi hit R hR
  exact step (residueIndex B) dims

include powers in
theorem chart_slice_weight (hp : p.measurable O v hO P S) (sub : c.support ⊆ p.value.support) :
    ∃ h : isRVSet _ S (unitSet O v (residueIndex c.frame) (p.onSlice c)),
      unitWeight O v hv hO P S (residueIndex c.frame) (p.onSlice c) h =
        p.residueWeight O v hv hO P S hp * entireUnitWeight O v hv hO P S 1 ^ (p.value.rank - c.rank) := by
  obtain ⟨α,hα,hi⟩ := c.independent
  have hit := Set.image_subset_range _ _ (sub (show c.frame.eval α ∈ c.support from ⟨α,hα,rfl⟩))
  exact frame_slice_weight O v hv hO P powers S p.value.frame c.frame p.residue hp α hi hit

end GeneralizedEuler.Section4
