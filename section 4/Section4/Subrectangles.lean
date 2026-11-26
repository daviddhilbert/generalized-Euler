module

public import Section4.NormalRectangles
public import Section4.RectangleFiberFamilies
import all Section4.NormalRectangles
import all Section4.ResidueWeights
import all Section4.RectangleClasses
import all Section4.DefinableResidueMatrices
import all Section4.CanonicalChartMaps
import all Section4.RectangleFiberFamilies
import all Section4.TaggedFiberMatching
import all Section4.FiniteScissors

/-! Restrictions in residue and value coordinates of a normalized
rectangle. The original height and the homogeneous degree are retained. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k : ℕ}

structure Subrectangle (c : NormalRectangle (JG := JG) (G := G) O v hO P S k) where
  units : Set (Fin c.m → v.ker)
  values : Set (Fin c.r → Additive O.ValueGroupˣ)
  unitsDef : isRVSet _ S (unitSet O v (Equiv.refl _) units)
  valuesDef : (G : Set (Additive O.ValueGroupˣ)).Definable JG values
  unitsSub : units ⊆ c.units
  valuesSub : values ⊆ c.values

namespace Subrectangle
variable {c : NormalRectangle (JG := JG) (G := G) O v hO P S k} (p : Subrectangle c)

def rect : NormalRectangle (JG := JG) (G := G) O v hO P S k :=
  ⟨c.m,c.r,c.degree,p.units,p.values,p.unitsDef,p.valuesDef⟩

def labels := p.units ×ˢ p.values
def points := productSet (unitSet O v (Equiv.refl _) p.units) (positiveSharp O v p.values)

theorem points_sub : p.points ⊆ c.points :=
  fun _ ⟨⟨u,h,eu⟩,⟨x,a,ex⟩⟩ => ⟨⟨u,p.unitsSub h,eu⟩,⟨x,p.valuesSub a,ex⟩⟩

theorem mem_points {u : Fin c.m → v.ker} {x : Fin c.r → Additive (PositiveRV O)} :
    Sum.elim (unitTuple O v (Equiv.refl _) u) (codeTuple O x) ∈ p.points ↔ (u,v ∘ x) ∈ p.labels := by
  constructor
  · rintro ⟨⟨w,h,eq⟩,⟨y,hy,e⟩⟩
    exact ⟨unitTuple_injective O v (Equiv.refl _) eq ▸ h,codeTuple_injective O e ▸ hy⟩
  · exact fun h => ⟨⟨u,h.1,rfl⟩,⟨x,h.2,rfl⟩⟩

end Subrectangle

variable (c : NormalRectangle (JG := JG) (G := G) O v hO P S k)
  {I : Type} [Fintype I] (a : I → Subrectangle c)

theorem residue_remainder_definable (T : Finset I) :
    isRVSet _ S (unitSet O v (Equiv.refl _) (c.units \ ⋃ i ∈ T, (a i).units)) := by
  classical
  have cut := isRVSet_iUnion (fun i : T => (a i.val).unitsDef)
  have hc : isRVSet _ S (⋃ i : T, unitSet O v (Equiv.refl _) (a i.val).units)ᶜ := cut.compl
  have defined := isRVSet_inter c.unitsDef hc
  refine (show unitSet O v (Equiv.refl _) (c.units \ ⋃ i ∈ T, (a i).units) =
      unitSet O v (Equiv.refl _) c.units ∩ (⋃ i : T, unitSet O v (Equiv.refl _) (a i.val).units)ᶜ from ?_).symm ▸ defined
  ext x
  constructor
  · rintro ⟨u,⟨hu,miss⟩,rfl⟩
    refine ⟨⟨u,hu,rfl⟩,?_⟩
    intro h
    obtain ⟨i,w,hw,eq⟩ := Set.mem_iUnion.mp h
    exact miss (Set.mem_iUnion.mpr ⟨i.val,Set.mem_iUnion.mpr ⟨i.property,unitTuple_injective O v (Equiv.refl _) eq ▸ hw⟩⟩)
  · rintro ⟨⟨u,hu,rfl⟩,miss⟩
    refine ⟨u,⟨hu,?_⟩,rfl⟩
    intro h
    obtain ⟨i,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨it,hi⟩ := Set.mem_iUnion.mp h
    exact miss (Set.mem_iUnion.mpr ⟨⟨i,it⟩,u,hi,rfl⟩)

end GeneralizedEuler.Section4.NormalRectangle
