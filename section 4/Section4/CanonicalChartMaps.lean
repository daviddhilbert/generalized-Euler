module

public import Section4.CanonicalRectangles
public import Section4.DefinableLifts
public import Section4.FiniteScissors
import all Section4.Scissors
import all Section2.RVDefinableEquivalence
import all Section4.PositiveRectangles
import all Section4.RectangleDecomposition
import all Section2.RVVectorSpace
import all Section2.DefinableAffineCharts

/-! Fixed-base definable chart morphisms in the actual RV sort. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))]
  [Module F (Additive O.ValueGroupˣ)]

def positiveCode : PositiveRV O →* RV0 O where
  toFun := positiveRVToRV0 O
  map_one' := positiveRVToRV0_one O
  map_mul' := positiveRVToRV0_mul O

def codeTuple {I : Type*} (t : I → Additive (PositiveRV O)) : I → RV0 O :=
  fun i => positiveRVToRV0 O (t i).toMul

theorem codeTuple_injective {I : Type*} : Function.Injective (codeTuple (I := I) O) := by
  intro x y e; funext i
  exact Additive.toMul.injective (positiveRVToRV0_injective O (congrFun e i))

variable (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul =
    P e (positiveRVToRV0 O x.toMul))

omit [Module F (Additive O.ValueGroupˣ)] in
include powers in
theorem code_affine {n m} (a : Matrix (Fin n) (Fin m) F)
    (u : Fin n → Additive (PositiveRV O)) (x : Fin m → Additive (PositiveRV O)) :
    rvAffineMonomial O P a (codeTuple O u) (codeTuple O x) = codeTuple O (actRows a x + u) := by
  funext i
  change positiveRVToRV0 O (u i).toMul * _ =
    (positiveCode O) ((∑ j, a i j • x j) + u i).toMul
  rw [toMul_add,map_mul,mul_comm (G := RV0 O) _ ((positiveCode O) (u i).toMul)]
  congr 1
  rw [toMul_sum,map_prod]
  rw [Finset.prod_map_toList (M := RV0 O) (Finset.univ : Finset (Fin m)) (fun j => P (a i j) (codeTuple O x j))]
  exact Finset.prod_congr rfl fun j _ => (powers (a i j) (x j)).symm

variable (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O))
  {G : Submodule F (Additive O.ValueGroupˣ)} {n r m : ℕ}
  (A : ValueFrame G r n) (omitCoord : Fin m ≃ A.dependent)

def codeRectangle (w : (Fin r → Additive (PositiveRV O)) × (A.dependent → v.ker)) :
    Fin m ⊕ Fin r → RV0 O :=
  Sum.elim (fun i => positiveRVToRV0 O (w.2 (omitCoord i)).val.toMul) (codeTuple O w.1)

theorem codeRectangle_injective :
    Function.Injective (codeRectangle O v A omitCoord) := by
  intro x y h
  apply Prod.ext
  · apply codeTuple_injective O
    exact funext fun i => congrFun h (.inr i)
  · funext i
    obtain ⟨j,rfl⟩ := omitCoord.surjective i
    apply Subtype.ext
    exact Additive.toMul.injective (positiveRVToRV0_injective O (congrFun h (.inl j)))

include powers in
theorem chart_on_assembled (z : Fin r → Additive (PositiveRV O)) (b : A.dependent → v.ker) :
    affineChartTuple O P A.free (fun i => (omitCoord i).val)
      (fun i => A.rows (omitCoord i).val) (fun i => positiveRVToRV0 O (s (A.shift (omitCoord i).val).val).toMul)
      (codeTuple O (A.assemble v s z b)) = codeRectangle O v A omitCoord (z,b) := by
  have hf := ValueFrame.assemble_free (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v s A z b
  have free : codeTuple O (A.assemble v s z b) ∘ A.free = codeTuple O z := by
    change codeTuple O (A.assemble v s z b ∘ A.free) = _
    rw [hf]
  funext i
  cases i with
  | inr j => exact congrFun free j
  | inl j =>
    change _ / rvAffineMonomial O P _ _ _ j = _
    rw [free,show (fun i => positiveRVToRV0 O (s (A.shift (omitCoord i).val).val).toMul) =
      codeTuple O (fun i => s (A.shift (omitCoord i).val).val) from rfl,
      code_affine O P powers]
    let d := A.lift s z (omitCoord j).val
    have h := A.extend_dependent (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v b (omitCoord j)
    change positiveRVToRV0 O (d + (A.extendResidues v b (omitCoord j).val).val).toMul /
      positiveRVToRV0 O d.toMul = positiveRVToRV0 O (b (omitCoord j)).val.toMul
    rw [h,toMul_add,positiveRVToRV0_mul,mul_comm (G := RV0 O)]
    rw [div_eq_mul_inv (G := RV0 O),mul_assoc (G := RV0 O),
      mul_inv_cancel₀ (G₀ := RV0 O) ((positiveRVToRV0_pos O d.toMul).ne_zero O),mul_one (M := RV0 O)]

variable {J : Language} [J.Structure K] [J.Structure (Residue O)]
  (hO : IsOrderConvex O) (C : SortedSubstructure (canonicalStructure (L := J) O hO P))

include powers in
/-- An actual chart bijection over the original substructure. The graph is
the sorted formula dividing by named monomial lifts. No formula for the
splitting section occurs in the graph. -/
theorem chart_definably_equivalent
    (W : Set ((Fin r → Additive (PositiveRV O)) × (A.dependent → v.ker)))
    (base : ∀ i, positiveRVToRV0 O (s (A.shift i).val).toMul ∈ C.carrier .rv)
    (hd : isRVSet _ C ((fun w => codeTuple O (A.assemble v s w.1 w.2)) '' W)) :
    RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) C.carrier
      ((fun w => codeTuple O (A.assemble v s w.1 w.2)) '' W) (codeRectangle O v A omitCoord '' W) := by
  let f (w : (Fin r → Additive (PositiveRV O)) × (A.dependent → v.ker)) :=
    codeTuple O (A.assemble v s w.1 w.2)
  let d := f '' W
  let y := codeRectangle O v A omitCoord
  have hf : Function.Injective f := (codeTuple_injective O).comp
    (A.assemble_injective (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v s)
  let ef := Equiv.Set.imageOfInjOn f W hf.injOn
  let ey := Equiv.Set.imageOfInjOn y W (codeRectangle_injective O v A omitCoord).injOn
  let e := ef.symm.trans ey
  let u (i : Fin m) : C.carrier .rv := ⟨_,base (omitCoord i).val⟩
  let a (i : Fin m) := A.rows (omitCoord i).val
  let normalize := affineChartTuple O P A.free (fun i => (omitCoord i).val) a (fun i => (u i).val)
  refine ⟨e,?_⟩
  have he (x : d) : (e x).val = normalize x.val := by
    obtain ⟨w,rfl⟩ := ef.surjective x
    change y (ef.symm (ef w)).val = normalize (f w.val)
    rw [ef.symm_apply_apply]
    exact (chart_on_assembled O P powers v s A omitCoord w.val.1 w.val.2).symm
  change SortedDefinableOver _ _ (rvGraph (X := CanonicalSort O) (D := d) (fun x : d => (e x).val))
  simp_rw [he]
  exact definable_affineChartTuple_graph O hO P d hd A.free (fun i => (omitCoord i).val) a u

theorem rectangle_image (D : Set (Fin r → Additive (PositiveRV O))) (B : Set (A.dependent → v.ker)) :
    codeRectangle O v A omitCoord '' (D ×ˢ B) = productSet
      ((fun b : A.dependent → v.ker => fun i => positiveRVToRV0 O (b (omitCoord i)).val.toMul) '' B)
      (codeTuple O '' D) := by
  ext x
  constructor
  · rintro ⟨⟨z,b⟩,⟨hz,hb⟩,rfl⟩; exact ⟨⟨b,hb,rfl⟩,z,hz,rfl⟩
  · rintro ⟨⟨b,hb,eb⟩,⟨z,hz,ez⟩⟩
    exact ⟨(z,b),⟨hz,hb⟩,funext (fun i => by cases i with | inl j => exact congrFun eb j | inr j => exact congrFun ez j)⟩

end GeneralizedEuler.Section4
