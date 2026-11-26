module

public import Section4.Subrectangles
public import Section4.RefinedFamilyBijection
import all Section4.NormalRectangles
import all Section4.Subrectangles
import all Section4.RectangleFiberFamilies
import all Section4.RefinedFamilyBijection
import all Section4.RVTaggedEquivalence
import all Section4.TaggedFiberMatching
import all Section4.DefinableResidueMatrices
import all Section4.CanonicalChartMaps
import all Section4.ResidueWeights
import all Section4.RectangleClasses

/-! Realize a rectangular partition inside its original tagged RV
family and transport its pieces to rectangles of smaller height. -/
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
  {G : Submodule F (Additive O.ValueGroupˣ)} {k l : ℕ}
variable {I H : Type} [Finite I] [Finite H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable {count : I → ℕ} (b : ∀ i, Fin (count i) → Subrectangle (c i))

@[expose] def subfamily : RVFamily.Subfamily (rvFamily c pull) where
  Tag := (i : I) × Fin (count i)
  parent t := t.1
  piece t := (b t.1 t.2).points
  definable t := (b t.1 t.2).definable_points pull
  subset t := (b t.1 t.2).points_sub

theorem subfamily_range (x : (fiberFamily c).Lift (T := Additive (PositiveRV O)) v) :
    fiberEquiv c pull x ∈ Set.range (subfamily c pull b).includePoint ↔
      ∃ t, (x.1.2.val,v ∘ x.2.val) ∈ (b x.1.1 t).labels := by
  obtain ⟨⟨i,u⟩,z⟩ := x
  constructor
  · rintro ⟨⟨⟨j,t⟩,w⟩,e⟩
    obtain rfl : j=i := congrArg Sigma.fst e
    have eq : w.val = Sum.elim (unitTuple O v (Equiv.refl _) u.val) (codeTuple O z.val) :=
      congrArg (fun x : (rvFamily c pull).piece j => x.val) (Sigma.mk.inj_iff.mp e).2.eq
    exact ⟨t,(Subrectangle.mem_points (b j t)).mp (eq ▸ w.property)⟩
  · rintro ⟨t,ht⟩
    exact ⟨⟨⟨i,t⟩,_,(Subrectangle.mem_points (b i t)).mpr ht⟩,rfl⟩

theorem subfamily_injective (disj : ∀ i, Pairwise (fun t t' => Disjoint (b i t).labels (b i t').labels)) :
    Function.Injective (subfamily c pull b).includePoint := by
  apply RVFamily.Subfamily.include_injective
  rintro ⟨i,t⟩ ⟨j,t'⟩ x y e
  obtain rfl : i=j := congrArg Sigma.fst e
  have eq : x.val = y.val := congrArg (fun z : (rvFamily c pull).piece i => z.val) (Sigma.mk.inj_iff.mp e).2.eq
  obtain ⟨u,hu,eu⟩ := x.property.1
  obtain ⟨z,hz,ez⟩ := x.property.2
  have same : Sum.elim (unitTuple O v (Equiv.refl _) u) (codeTuple O z) = x.val := funext (Sum.rec (congrFun eu) (congrFun ez))
  have hy : (u,v ∘ z) ∈ (b i t').labels := (Subrectangle.mem_points (b i t')).mp ((same.trans eq).symm ▸ y.property)
  have hx : (u,v ∘ z) ∈ (b i t).labels := ⟨hu,hz⟩
  exact congrArg (Sigma.mk i) (Classical.byContradiction fun ne => Set.disjoint_left.mp (disj i ne) hx hy)

theorem subfamily_iso_normal
    (q : ((i : I) × Fin (count i)) → NormalRectangle (JG := JG) (G := G) O v hO P S k)
    (iso : ∀ i t, RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (b i t).points (q ⟨i,t⟩).points) :
    (subfamily c pull b).family.Iso (rvFamily q pull) :=
  RVFamily.iso_retag _ _ (Equiv.refl _) (fun t => iso t.1 t.2)

end GeneralizedEuler.Section4.NormalRectangle
