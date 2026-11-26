module

public import Section4.SelectedSharpFibers
public import Section4.TaggedMeasureComparison
public import Section4.SignedValueReflection
import all Section4.SelectedSharpFibers
import all Section4.LocalRVMeasure
import all Section4.TaggedMatchGraph
import all Section4.UnitFiberNormalization
import all Section4.ValuePullback
import all Section4.SignedRectangleFactors
import all Section4.UnaryTaggedComparison
import all Section4.Factors

/-! Division by base representatives identifies each full signed unary
fiber with the positive residue line. Applying its o-minimal Euler
characteristic counts the fibers with their multiplicities. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
  (hO : IsOrderConvex O) {J H : Language} [J.Structure K] [J.Structure (Residue O)]
  [H.Structure (SignedValueGroup O)] (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable H D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)

local notation "M" => canonicalStructure (L := J) O hO P
local notation "val" => signedLabel O hO

def positiveUnitLine : Set (Fin 1 → RV0 O) := sharp M val {1}

def positiveUnit (t : RV0 O) : Prop := t ≠ 0 ∧ val t = 1

include defSharp in
theorem positiveUnitLine_good (he : A.Definable H ({1} : Set (Fin 1 → SignedValueGroup O))) :
    GoodRVSet M S (positiveUnit O hO) (positiveUnitLine (J := J) O hO P) :=
  ⟨defSharp he,fun _ hx i => ⟨hx.1 i,congrFun hx.2 i⟩⟩

include witness defSharp in
theorem signed_point_fiber_equivalent (a : Fin 1 → SignedValueGroup O) (ha : A.Definable H {a}) :
    RVDefinablyEquivalent M S.carrier (sharp M val {a}) (positiveUnitLine (J := J) O hO P) := by
  let D := sharp M val {a}
  choose t nt ht using fun i => signedLabel_rep O hO (a i)
  have hD : D.Nonempty := ⟨t,nt,funext ht⟩
  obtain ⟨y,hy,old⟩ := witness D (defSharp ha) hD
  have ny : ∀ i, y i ≠ 0 := hy.1
  have labels : val ∘ y = a := hy.2
  have eq : (fun x => x / y) '' D = positiveUnitLine (J := J) O hO P := by
    ext z; constructor
    · rintro ⟨x,hx,rfl⟩
      have nx : ∀ i, x i ≠ 0 := hx.1
      have equal : val ∘ x = a := hx.2
      have nz i := div_ne_zero (G₀ := RV0 O) (nx i) (ny i)
      refine ⟨nz,funext fun i => ?_⟩
      have eq := signedLabel_mul O hO (nz i) (ny i)
      rw [div_mul_cancel₀ (G₀ := RV0 O) _ (ny i)] at eq
      apply mul_right_cancel (b := val (y i))
      exact eq.symm.trans ((congrFun (equal.trans labels.symm) i).trans (one_mul _).symm)
    · intro hz
      have nz : ∀ i, z i ≠ 0 := hz.1
      have line : val ∘ z = 1 := hz.2
      refine ⟨z*y,⟨fun i => mul_ne_zero (nz i) (ny i),funext fun i => ?_⟩,funext fun i => (Units.mk0 (y i) (ny i)).mul_left_inj.mp (div_mul_cancel₀ (G₀ := RV0 O) (z i * y i) (ny i))⟩
      change val (z i * y i) = a i
      rw [signedLabel_mul O hO (nz i) (ny i),show val (z i)=1 from congrFun line i,one_mul]
      exact congrFun labels i
  rw [← eq]; exact divide_fiber_equivalent O hO P S D (defSharp ha) y old ny

variable (he : A.Definable H ({1} : Set (Fin 1 → SignedValueGroup O)))
local notation "good" => positiveUnitLine_good O hO P S A defSharp he
variable (μ : LocalRVMeasure (canonicalStructure (L := J) O hO P) S (positiveUnit O hO) 1 ℤ)
  (chi : μ.weight (positiveUnitLine (J := J) O hO P) (positiveUnitLine_good O hO P S A defSharp he) = -1)

include witness he chi in
theorem finite_fiber_euler_counts (U W : Over (J := H) A 1) (D : Set (U.points A)) (E : Set (W.points A))
    {n m} (e : Fin n ≃ D) (g : Fin m ≃ E)
    (de : ∀ i, A.Definable H {pointTuple U (e i).val}) (dg : ∀ j, A.Definable H {pointTuple W (g j).val})
    (iso : (selectedFamily (S := S) val A defSharp U D e de).Iso (selectedFamily (S := S) val A defSharp W E g dg)) :
    -(n : ℤ) = -(m : ℤ) := by
  let family (V : Over (J := H) A 1) (Q : Set (V.points A)) {l : ℕ} (j : Fin l ≃ Q)
      (dj : ∀ t, A.Definable H {pointTuple V (j t).val}) := selectedFamily (S := S) val A defSharp V Q j dj
  let cell (V : Over (J := H) A 1) (Q : Set (V.points A)) {l : ℕ} (j : Fin l ≃ Q)
      (dj : ∀ t, A.Definable H {pointTuple V (j t).val}) (i : Fin l) : LocalRVMeasure.Cell M S (positiveUnit O hO) 1 (Fin 1) :=
    ⟨(family V Q j dj).piece i,(family V Q j dj).definable i,positiveUnitLine (J := J) O hO P,good,
      signed_point_fiber_equivalent O hO P S A defSharp @witness _ (dj i)⟩
  let a := selectedFamily (S := S) val A defSharp U D e de
  let b := selectedFamily (S := S) val A defSharp W E g dg
  obtain ⟨f,hf⟩ := iso
  have eq := @RVFamily.sum_cells_eq _ _ _ M S a b f hf (Fin.fintype n) (Fin.fintype m) _ 1 ℤ _ μ
    (cell U D e de) (cell W E g dg) (fun _ => rfl) (fun _ => rfl)
  change (∑ _ : Fin n, μ.weight _ good) = ∑ _ : Fin m, μ.weight _ good at eq
  simpa [chi] using eq

end GeneralizedEuler.Section4
