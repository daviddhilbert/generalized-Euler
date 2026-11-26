module

public import Section4.RectangleProducts
import all Section4.ValueFactorMap
import all Section4.Scissors

/-! Coordinate projections removing an empty tuple are fixed-base
definable bijections, in both orders of the product. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {I : Type} [Finite I] {D : Set (I → Z .rv)} (hd : isRVSet M S D)

include hd in
theorem rv_empty_product_left : RVDefinablyEquivalent M S.carrier D (productSet (Set.univ : Set (Fin 0 → Z .rv)) D) := by
  have e := rv_reindex_equivalent M S (Equiv.emptySum (Fin 0) I) D hd
  have eq : {y | y ∘ (Equiv.emptySum (Fin 0) I).symm ∈ D} = productSet (Set.univ : Set (Fin 0 → Z .rv)) D :=
    Set.ext fun _ => ⟨fun h => ⟨Set.mem_univ _,h⟩,fun h => h.2⟩
  rwa [eq] at e

include hd in
theorem rv_empty_product_right : RVDefinablyEquivalent M S.carrier D (productSet D (Set.univ : Set (Fin 0 → Z .rv))) := by
  have e := rv_reindex_equivalent M S (Equiv.sumEmpty I (Fin 0)) D hd
  have eq : {y | y ∘ (Equiv.sumEmpty I (Fin 0)).symm ∈ D} = productSet D (Set.univ : Set (Fin 0 → Z .rv)) :=
    Set.ext fun _ => ⟨fun h => ⟨h,Set.mem_univ _⟩,fun h => h.1⟩
  rwa [eq] at e

end GeneralizedEuler.Section4
