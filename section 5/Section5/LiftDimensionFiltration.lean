module

public import Section5.LiftFieldObjects
public import Section3.DefinableFunctions

/-! Every nonempty lift of a degree-k RV object has VF dimension k.
A fixed RV tag gives a product of open, nonzero leading-term fibers. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)} {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem lift_vfDimension_of_nonempty
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (U : RVObject 𝓜 S k) (nonempty : U.carrier.Nonempty) :
    vfDimension (mixedTuple '' ObjectLift.carrier U) = k := by
  classical
  have upper : vfDimension (mixedTuple '' ObjectLift.carrier U) ≤ k :=
    ambient_vf_dimension_bound (mixedTuple '' ObjectLift.carrier U)
  refine le_antisymm upper ?_
  obtain ⟨u,hu⟩ := nonempty
  let tag : U.carrier := ⟨u,hu⟩
  let P (i : Fin k) : Set K := {x | rv O x = U.label tag i}
  let B : Set (Fin k → K) := Set.pi Set.univ P
  have openP (i : Fin k) : IsOpen (P i) := by
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have value : rv O x = U.label tag i := hx
    have nz : x ≠ 0 := fun e => U.nonzero tag i (by
      change U.label tag i = 0
      rw [← value,e,map_zero])
    have small' : O.valuation |eps| < 1 := (valuation_abs O eps).trans_lt small
    have ev := eventually_rv_eq O hO (abs_pos.2 he) small' nz
    exact ev.mono (fun z hz => hz.trans value)
  have openB : IsOpen B := isOpen_set_pi Set.finite_univ (fun i _ => openP i)
  choose x hx using fun i => rv_surjective O (U.label tag i)
  have mem : x ∈ B := fun i _ => hx i
  let D := sortedFiber (mixedTuple '' ObjectLift.carrier U) u
  have sub : B ⊆ D := by
    intro y hy
    let a : SortedAssignment Z (ObjectLift.Vars U) := fun | .vf => y | .rv => u
    refine ⟨a,⟨tag,rfl,?_⟩,rfl⟩
    funext i
    exact ((hy i (Set.mem_univ i)).symm).trans ((canonicalStructure_rvMap O hO power (y i)).symm)
  have projection : HasInteriorProjection (k := k) D := by
    let e : Fin k ↪ Fin k := Function.Embedding.refl _
    have cover : B ⊆ coordinateProjection e '' D := fun y hy => ⟨y,sub hy,rfl⟩
    have inside : x ∈ interior B := openB.interior_eq.symm ▸ mem
    exact ⟨e,x,interior_mono cover inside⟩
  exact (le_projectionDimension projection).trans (projectionDimension_fiber_le_vfDimension _ _)

end GeneralizedEuler.Section5
