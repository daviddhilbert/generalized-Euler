module

public import Section4.StandardRectangleWeight
public import Section4.ObjectTensorWeights
public import Section4.RectangleProducts
import all Section4.ResidueProducts
import all Section4.ObjectTensorWeights
import all Section4.LocalRVMeasure
import all Section4.PositiveValuation
import all Section4.ValueScissors
import all Section4.StandardRectangleWeight
import all Section4.ResidueWeights
import all Section4.RectangleClasses
import all Section4.RVProducts

/-! Homogeneous normalized rectangles and their assigned tensors,
including value domains of smaller rank than their ambient arity. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] {G : Submodule F (Additive O.ValueGroupˣ)}
local instance rectangleObjectUnsignedStructure : JG.Structure O.ValueGroupˣ :=
  inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (lang : ValueLanguage (J := JG) G)
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
variable [Algebra C R] [Algebra C W] (e : C) (Rmap : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R) (Vmap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)
  (resBalance : algebraMap C R e = Rmap (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = Vmap (eValue (J := JG) G))

variable {n : ℕ}

variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable {k : ℕ}

variable (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))
variable (complete : ∀ {n} (U : Set (Fin n → RV0 O)), isRVSet _ S U → (∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) →
  AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' U))

structure NormalRectangle (k : ℕ) where
  m : ℕ
  r : ℕ
  degree : m+r = k
  units : Set (Fin m → v.ker)
  values : Set (Fin r → Additive O.ValueGroupˣ)
  unitsDef : isRVSet _ S (unitSet O v (Equiv.refl _) units)
  valuesDef : (G : Set _).Definable JG values

namespace NormalRectangle
variable {O v hO P S} (c : NormalRectangle (JG := JG) (G := G) O v hO P S k)
def points := productSet (unitSet O v (Equiv.refl _) c.units) (positiveSharp O v c.values)
def tensor : TensorProduct C R W := Rmap (unitWeight O v hv hO P S (Equiv.refl _) c.units c.unitsDef) ⊗ₜ[C]
  Vmap (pieceClass c.values c.valuesDef)

variable (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D → isRVSet _ S (positiveSharp O v D))

include pull in
theorem points_definable : isRVSet (canonicalStructure (L := J) O hO P) S c.points := rv_product_definable c.unitsDef (pull c.valuesDef)

include pull in
theorem assigned : (tensorLocalMeasure (k := k) O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete).assigned c.points
    (c.tensor hv Rmap Vmap (C := C)) := by
  obtain ⟨m,r,deg,B,D,hb,hd⟩ := c
  subst k
  let M := canonicalStructure (L := J) O hO P
  let μ : LocalRVMeasure M S (IsPositiveRV O) (m+r) (TensorProduct C R W) :=
    tensorLocalMeasure O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete
  let U := unitSet O v (Equiv.refl _) B
  let V := positiveSharp O v D
  let packed := cartesian U V
  have hg : isRVSet M S (productSet U V) := rv_product_definable hb (pull hd)
  have iso : RVDefinablyEquivalent M S.carrier (productSet U V) packed := rv_reindex_equivalent M S finSumFinEquiv.symm _ hg
  have good : GoodRVSet M S (IsPositiveRV O) packed := by
    refine ⟨rv_equivalent_target_definable iso,?_⟩
    intro x hx i
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin r ≃ Fin (m+r)).surjective i
    cases j with
    | inl i => exact unitSet_positive O v (Equiv.refl _) B _ hx.1 i
    | inr j => exact positiveSharp_pos O v D _ hx.2 j
  have model := μ.assigned_model packed good
  have weight := standard_rectangle_weight O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat D hd B hb
  rw [← code_cartesian O v B D] at weight
  have val : μ.weight packed good =
      Rmap (unitWeight O v hv hO P S (Equiv.refl _) B hb) ⊗ₜ[C] Vmap (pieceClass D hd) :=
    single_chart_weight O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat
      (positiveSetWeight_spec O v hv hO P S Rmap Vmap s complete packed good.1 good.2) weight
  rw [val] at model
  exact μ.transfer iso model

variable {l : ℕ} (d : NormalRectangle (JG := JG) (G := G) O v hO P S l)

include pull in
theorem product_rectangle :
    ∃ z : NormalRectangle (JG := JG) (G := G) O v hO P S (k+l),
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (productSet c.points d.points) z.points ∧
      z.tensor hv Rmap Vmap = c.tensor hv Rmap Vmap * d.tensor hv Rmap Vmap (C := C) := by
  obtain ⟨hu,eq⟩ := unit_product O v hv hO P S (Equiv.refl _) (Equiv.refl _) c.units d.units c.unitsDef d.unitsDef
  have degree : (c.m+d.m)+(c.r+d.r) = k+l := by have := c.degree; have := d.degree; omega
  let z : NormalRectangle (JG := JG) (G := G) O v hO P S (k+l) :=
    ⟨_,_,degree,_,cartesian c.values d.values,hu,cartesian_definable c.valuesDef d.valuesDef⟩
  refine ⟨z,?_,?_⟩
  · have shuffle := productSet_shuffle c.unitsDef (pull c.valuesDef) d.unitsDef (pull d.valuesDef)
    have pack := rv_product_equivalent (productSet_cartesian c.unitsDef d.unitsDef)
      (productSet_cartesian (pull c.valuesDef) (pull d.valuesDef))
    unfold points
    dsimp only [z]
    rw [packedProduct_code,positiveSharp_product]
    exact shuffle.trans pack
  · change Rmap (unitWeight O v hv hO P S _ _ hu) ⊗ₜ[C] Vmap (pieceClass _ _) = _
    rw [eq,pieceClass_product c.valuesDef d.valuesDef,map_mul,map_mul]
    simp only [tensor, Algebra.TensorProduct.tmul_mul_tmul]

end NormalRectangle
end GeneralizedEuler.Section4
