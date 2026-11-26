module

public import Section4.ResidueMatrices
public import Section4.SignedRectangleFactors
import all Section4.CanonicalChartMaps
import all Section4.DefinableLifts
import all Section2.RVVectorSpace
import all Section2.SortedStructure

/-! Fixed-base definability for linear forms on positive residue coordinates. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
set_option backward.isDefEq.respectTransparency false
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  {I H : Type} {m n : ℕ} (ei : Fin m ≃ I) (eo : Fin n ≃ H)

local instance kernelGroup : AddCommGroup v.ker := @Submodule.addCommGroup F (Additive (PositiveRV O)) _ _ _ v.ker
local instance kernelModule : Module F v.ker := @Submodule.module F (Additive (PositiveRV O)) _ _ _ v.ker

def unitTuple (x : I → v.ker) : Fin m → RV0 O := codeTuple O (v.ker.subtype ∘ x ∘ ei)

theorem unitTuple_injective : Function.Injective (unitTuple O v ei) := by
  intro x y h
  have eq := codeTuple_injective O h
  funext i
  obtain ⟨j,rfl⟩ := ei.surjective i
  exact Subtype.ext (congrFun eq j)

variable [Fintype I] (A : Matrix H I F) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))

include powers in
theorem unitTuple_matrix (x : I → v.ker) : unitTuple O v eo (actRows A x) =
    rvAffineMonomial O P (fun i j => A (eo i) (ei j)) (fun _ => 1) (unitTuple O v ei x) := by
  have hz : codeTuple O (0 : Fin n → Additive (PositiveRV O)) = 1 := rfl
  rw [show (fun _ : Fin n => (1 : RV0 O)) = codeTuple O (0 : Fin n → Additive (PositiveRV O)) from hz.symm]
  change _ = rvAffineMonomial O P _ _ (codeTuple O (v.ker.subtype ∘ x ∘ ei))
  rw [code_affine O P powers,add_zero]
  apply congrArg (codeTuple O)
  funext i
  change (actRows A x (eo i)).val = _
  rw [show (actRows A x (eo i)).val = actRows A (v.ker.subtype ∘ x) (eo i) from
    by change v.ker.subtype (∑ j, A (eo i) j • x j) = ∑ j, A (eo i) j • v.ker.subtype (x j); rw [map_sum]; simp]
  exact (ei.sum_comp (fun j => A (eo i) j • (x j).val)).symm

variable {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

include powers in
theorem unit_matrix_graph (D : Set (I → v.ker)) (hd : isRVSet _ S (unitTuple O v ei '' D))
    (f : (unitTuple O v ei '' D) → Fin n → RV0 O)
    (spec : ∀ x (hx : x ∈ D), f ⟨unitTuple O v ei x,⟨x,hx,rfl⟩⟩ = unitTuple O v eo (actRows A x)) :
    SortedDefinableOver (canonicalStructure (L := J) O hO P) S.carrier (rvGraph f) := by
  have hOne : 1 ∈ S.carrier .rv := S.closed .rvOne (fun i => i.elim0) (fun i => i.elim0)
  let u (_ : Fin n) : S.carrier .rv := ⟨1,hOne⟩
  have eq : f = fun x => rvAffineMonomial O P (fun i j => A (eo i) (ei j)) (fun i => (u i).val) x.val := by
    funext y
    obtain ⟨t,ht,e⟩ := y.property
    obtain ⟨y,hy⟩ := y
    change unitTuple O v ei t = y at e
    subst y
    rw [spec t ht,unitTuple_matrix O v ei eo A P powers]
  rw [eq]
  exact definable_monomial_map O hO P S _ hd _ u

include powers in
theorem unit_matrix_equivalence (D : Set (I → v.ker)) (hd : isRVSet _ S (unitTuple O v ei '' D))
    (inj : Set.InjOn (actRows A) D) :
    RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (unitTuple O v ei '' D)
      (unitTuple O v eo '' (actRows A '' D)) := by
  let ex := Equiv.Set.imageOfInjOn _ D (unitTuple_injective O v ei).injOn
  let map := Equiv.Set.imageOfInjOn _ D inj
  let ey := Equiv.Set.imageOfInjOn _ (actRows A '' D) (unitTuple_injective O v eo).injOn
  let e := ex.symm.trans (map.trans ey)
  refine ⟨e,unit_matrix_graph O v ei eo A P powers hO S D hd _ ?_⟩
  intro x hx
  change (ey (map (ex.symm (ex ⟨x,hx⟩)))).val = _
  rw [ex.symm_apply_apply]; rfl

end GeneralizedEuler.Section4
