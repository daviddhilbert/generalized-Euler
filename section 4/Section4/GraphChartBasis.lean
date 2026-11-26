module

public import Section4.MeasurableCharts
public import Section4.ProjectedPieceWeights
import all Section4.SliceComparison
import all Section4.ProjectedFrame
import all Section4.ProjectedValuePiece
import all Section4.ProjectedRVChart
import all Section2.RVVectorSpace

/-! A nonempty injectively projected chart admits free coordinates in the
projection. The positive residue kernel supplies the perturbing unit. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  {v : T →ₗ[F] V} (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id)
  {G : Submodule F V} {J : Language} [J.Structure V] {n k : ℕ}
  (a : ChartPiece v G J n) (p : Fin k → Fin n)

include hs in
theorem graph_chart_basis (d : v.ker) (hd : d ≠ 0) (hb : a.residue.Nonempty)
    (inj : Set.InjOn (fun x : Fin n → T => x ∘ p) (a.carrier s)) :
    Nonempty (ProjectionBasis a.value.frame p) := by
  obtain ⟨α,hα,_⟩ := a.value.independent
  have hz : v ∘ (s ∘ α) ∈ a.value.domain := by
    have eq : v ∘ (s ∘ α) = α := funext fun i => DFunLike.congr_fun hs (α i)
    rwa [eq]
  obtain ⟨j,U,hU⟩ := full_rank_minor _ (a.value.frame.graph_full_rank v s p a.value.domain a.residue
    inj (s ∘ α) hz hb.choose hb.choose_spec d hd)
  exact ⟨j,U,hU⟩

namespace ProjectionBasis
variable {s a p} (q : ProjectionBasis a.value.frame p) (lang : ValueLanguage (J := J) G)
def imageChart : ChartPiece v G J k :=
  ⟨q.projectedPiece lang a.value.domain a.value.definable a.value.independent,q.projectResidues v '' a.residue⟩

include hs in
theorem imageChart_carrier : (q.imageChart lang).carrier s = (fun x : Fin n → T => x ∘ p) '' a.carrier s :=
  (q.projection_rectangle v s hs a.value.domain a.residue).symm
include hs in
theorem residue_injection (inj : Set.InjOn (fun x : Fin n → T => x ∘ p) (a.carrier s)) :
    Set.InjOn (q.projectResidues v) a.residue := by
  obtain ⟨α,hα,_⟩ := a.value.independent
  exact q.projectResidues_injOn v s hs a.value.domain ⟨α,hα⟩ a.residue inj

end ProjectionBasis

section Kernel
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)
  [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))

include hv hO in
theorem positive_kernel_nonzero : ∃ d : v.ker, d ≠ 0 := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := rvLinearOrder O hO
  let r : Residue O := 2
  have hr : 0 < r := by dsimp [r]; positivity
  have pos : IsPositiveRV O (residueRV O r) := (isPositiveRV_iff_pos O hO).mpr (by
    simpa only [residueRV_zero] using residueRV_strictMono O hO hr)
  obtain ⟨t,ht⟩ := exists_positiveRV_of_positive O pos
  have val : positiveValueMap O t = 1 := by
    apply Units.ext
    rw [positiveValueMap_coe,ht,Units.val_one]
    exact unsignedValue_residueRV_of_ne_zero O hr.ne'
  have zero : v (Additive.ofMul t) = 0 := by rw [hv]; exact val
  refine ⟨⟨Additive.ofMul t,zero⟩,fun eq => ?_⟩
  have one : t = 1 := congrArg (fun x : v.ker => x.val.toMul) eq
  have equal : residueRV O r = residueRV O 1 := by rw [← ht,one,residueRV_one]; rfl
  have bad : (2 : Residue O) = 1 := residueRV_injective O equal
  norm_num at bad

end Kernel
end GeneralizedEuler.Section4
