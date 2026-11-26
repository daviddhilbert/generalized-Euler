module

public import Section4.ChartIndependence
public import Section4.RectangleGeneration
import all Section4.PositiveRectangles
import all Section4.RectangleDecomposition
import all Section4.SliceComparison
import all Section4.SliceWeights
import all Section4.DefinableResidueMatrices
import all Section4.RectangleClasses
import all Section4.ResidueWeights

/-! Every positive partition supplied by the canonical rectangle theorem
gives measurable charts for the decomposition-independent tensor valuation. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
set_option backward.isDefEq.respectTransparency false

namespace PositivePiece
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  {v : T →ₗ[F] V} {G : Submodule F V} {J : Language} [J.Structure V] {n : ℕ}
  {Q : Set (Fin n → v.ker) → Prop}
  (p : PositivePiece v G (fun _ D => (G : Set V).Definable J D) Q)

def asChart : ChartPiece v G J n := ⟨p.value,p.residues⟩

theorem asChart_carrier (s : V →ₗ[F] T) (D : Set (Fin n → T))
    (chart : ∃ e : p.rectangle ≃ p.carrier D, ∀ z, (e z).val = p.value.frame.assemble v s z.1.val z.2.val) :
    p.asChart.carrier s = p.carrier D := by
  obtain ⟨e,he⟩ := chart
  ext x; constructor
  · rintro ⟨⟨z,b⟩,⟨hz,hb⟩,rfl⟩
    let w : p.rectangle := (⟨z,hz⟩,⟨b,hb⟩)
    change p.value.frame.assemble v s w.1.val w.2.val ∈ p.carrier D
    rw [← he w]; exact (e w).property
  · intro hx
    let w := e.symm ⟨x,hx⟩
    exact ⟨(w.1.val,w.2.val),⟨w.1.property,w.2.property⟩,(he w).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))⟩

end PositivePiece

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  {G : Submodule F (Additive O.ValueGroupˣ)} {J : Language} [J.Structure K] [J.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (base : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] (lang : ValueLanguage (J := JG) G)
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))


local instance presentationKernelGroup : AddCommGroup v.ker := @Submodule.addCommGroup F (Additive (PositiveRV O)) _ _ _ v.ker
local instance presentationKernelModule : Module F v.ker := @Submodule.module F (Additive (PositiveRV O)) _ _ _ v.ker

include hs powers base lang pull in
theorem measurable_positive_charts {n l} (U : Set (Fin n → RV0 O)) (hU : isRVSet _ S U)
    (pos : ∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) {Q : Set (Fin n → v.ker) → Prop}
    (p : Fin l → PositivePiece v G (fun _ D => (G : Set _).Definable JG D) Q)
    (supports : ∀ γ, ∃! i, γ ∈ (p i).value.support)
    (charts : ∀ i, ∃ e : (p i).rectangle ≃ (p i).carrier ((codeTuple O) ⁻¹' U), ∀ z,
      (e z).val = (p i).value.frame.assemble v s z.1.val z.2.val) :
    ∀ i, (p i).asChart.measurable O v hO P S := by
  obtain ⟨D,hd,_,eq,_⟩ := positive_partition_class O v s hs hO P powers S base lang @pull U hU pos p supports charts
  intro i
  obtain ⟨idx,hidx⟩ := eq i
  have h : isRVSet _ S (unitSet O v idx (p i).residues) := by
    change isRVSet _ S (codedResidues O v (p i).value.frame idx (p i).residues)
    rw [← hidx]; exact hd i
  let A := (p i).value.frame
  let I := A.dependent
  let f := readMatrix (F := F) (id : I → I)
  have hf : actRows (T := v.ker) f = id := funext fun x => act_read id x
  have inj := hf.symm ▸ (Function.injective_id (α := I → v.ker))
  have image := unit_matrix_equivalence O v idx (residueIndex A) f P powers hO S (p i).residues h inj.injOn
  rw [hf,Set.image_id] at image
  exact rv_equivalent_target_definable image

end GeneralizedEuler.Section4
