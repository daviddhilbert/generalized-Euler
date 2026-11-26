module

public import Section4.FiniteBaseFibers
public import Section4.SignedTensorFactors
import all Section4.SignedRectangleFactors
import all Section2.RVSplitCoordinates
import all Section2.RVMonomials
import all Section2.SignedValue
import all Section4.Objects

/-! A finite-value object has representatives over the original RV base
on each unsigned value tuple, including tuples with zero coordinates. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) {J : Language} [J.Structure K] [J.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

theorem unsignedValue_of_signedLabel (t : RV0 O) (ht : t ≠ 0) :
    unsignedValue O t = ((signedLabel O hO t).2 : O.ValueGroup) := by
  have h := signedToUnsigned_signedValue O hO t
  cases he : signedValue O hO t using WithZero.recZeroCoe with
  | zero => exact ((map_ne_zero _).mpr ht he).elim
  | coe u =>
    rw [he] at h
    rw [signedLabel,he]
    exact h.symm

theorem residue_unsigned_finite {n} (U : Set (Fin n → RV0 O))
    (fin : (Set.range (fun x : U => signedLabel O hO ∘ x.val)).Finite) :
    ((fun x => unsignedValue O ∘ x) '' U).Finite := by
  classical
  let D := Set.range (fun x : U => signedLabel O hO ∘ x.val)
  let d (j : Fin n) := insert 0 ((fun q : Fin n → SignedValueGroup O => ((q j).2 : O.ValueGroup)) '' D)
  have finite (j) : (d j).Finite := (fin.image _).insert _
  let types (j : Fin n) : Fintype (d j) := (finite j).fintype
  let f (x : ∀ j, d j) := fun j => (x j).val
  apply (Set.finite_range f).subset
  rintro _ ⟨x,hx,rfl⟩
  have mem j : unsignedValue O (x j) ∈ d j := by
    by_cases hz : x j = 0
    · simp [d,hz]
    · exact Or.inr ⟨_,⟨⟨x,hx⟩,rfl⟩,(unsignedValue_of_signedLabel O hO _ hz).symm⟩
  exact ⟨fun j => ⟨_,mem j⟩,rfl⟩

variable (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
include witness in
theorem residue_unsigned_representatives {n} (U : Set (Fin n → RV0 O)) (hd : isRVSet _ S U)
    (fin : (Set.range (fun x : U => signedLabel O hO ∘ x.val)).Finite)
    (x : U) : ∃ y ∈ U, (∀ i, y i ∈ S.carrier .rv) ∧ unsignedValue O ∘ y = unsignedValue O ∘ x.val := by
  have fiber (y : Fin n → RV0 O) (hy : ∀ i, y i ∈ S.carrier .rv) :
      isRVSet _ S {z : Fin n → RV0 O | unsignedValue O ∘ z = unsignedValue O ∘ y} := by
    have h := definable_unsigned_value_fiber (L := J) (Var := RVVariables (Fin n)) O hO P id
      (A := S.carrier) (fun i => ⟨y i,hy i⟩)
    unfold isRVSet
    convert h using 1; ext a; exact funext_iff
  exact finite_base_fibers (M := canonicalStructure (L := J) O hO P) (S := S) (fun t : Fin n → RV0 O => unsignedValue O ∘ t) witness fiber U hd
    (residue_unsigned_finite O hO U fin) _ ⟨x.val,x.property,rfl⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem valueCoordinate_eq_of_unsigned {x y : RV0 O} (h : unsignedValue O x = unsignedValue O y) :
    RVValueSection.valueCoordinate x = RVValueSection.valueCoordinate y := by
  by_cases hx : x = 0
  · subst x
    have hy : y = 0 := (map_eq_zero _).mp ((map_zero _).symm.trans h).symm
    rw [hy]
  · have hy : y ≠ 0 := fun e => hx ((map_eq_zero _).mp (h.trans (e ▸ map_zero _)))
    exact Units.ext ((RVValueSection.coe_valueCoordinate hx).trans (h.trans (RVValueSection.coe_valueCoordinate hy).symm))

end GeneralizedEuler.Section4
