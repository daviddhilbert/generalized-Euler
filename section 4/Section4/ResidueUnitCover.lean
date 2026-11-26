module

public import Section4.UnitFiberNormalization
public import Section4.FixedResidueImages
import all Section4.SignedRectangleFactors
import all Section4.Objects

/-! Partition a positive finite-value object into fixed-base unit charts.
The labels track the original degree even when a fiber is a singleton. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F] (O : ValuationSubring K)
  [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)

include hv witness in
theorem residue_unit_cover {n} (U : Set (Fin n → RV0 O)) (hu : isRVSet _ S U)
    (pos : ∀ x ∈ U, ∀ j, IsPositiveRV O (x j))
    (fin : (Set.range fun x : U => signedLabel O hO ∘ x.val).Finite) :
    ∃ (l : ℕ) (C : Fin l → Set (Fin n → RV0 O)) (B : Fin l → Set (Fin n → v.ker)),
      (∀ i, isRVSet _ S (C i)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ i, C i) = U ∧
      ∀ i, ∃ _hb : isRVSet _ S (unitSet O v (Equiv.refl _) (B i)),
        RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (C i) (unitSet O v (Equiv.refl _) (B i)) := by
  classical
  let label (x : Fin n → RV0 O) := signedValue O hO ∘ x
  let V := label '' U
  have finite : V.Finite := by
    let embed (z : Fin n → SignedValueGroup O) := fun j => (z j : WithZero (SignedValueGroup O))
    apply (fin.image embed).subset
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨_,⟨⟨x,hx⟩,rfl⟩,funext fun j => ?_⟩
    change ((↑((signedValue O hO (x j)).unzeroD (1 : SignedValueGroup O))) : WithZero (SignedValueGroup O)) = signedValue O hO (x j)
    cases h : signedValue O hO (x j) using WithZero.recZeroCoe with
    | zero => exact ((map_ne_zero _).mpr ((pos x hx j).ne_zero O) h).elim
    | coe z => rfl
  let : Fintype V := finite.fintype
  let e := (Fintype.equivFin V).symm
  have reps i := finite_base_fibers (M := canonicalStructure (L := J) O hO P) (S := S) label witness
    (signed_value_fiber_definable O hO P S) U hu finite (e i).val (e i).property
  choose y hy old eq using reps
  let C i := U ∩ {x | label x = label (y i)}
  have defC i : isRVSet _ S (C i) := hu.inter (signed_value_fiber_definable O hO P S (y i) (old i))
  have disj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j ne; apply Set.disjoint_left.mpr; intro x hx hj
    exact ne (e.injective (Subtype.ext (((eq i).symm.trans hx.2.symm).trans (hj.2.trans (eq j)))))
  have cov : (⋃ i, C i) = U := by
    ext x; rw [Set.mem_iUnion]
    refine ⟨fun ⟨_,h⟩ => h.1,fun h => ?_⟩
    let a : V := ⟨label x,x,h,rfl⟩
    exact ⟨e.symm a,h,(congrArg Subtype.val (e.apply_symm_apply a)).symm.trans (eq _).symm⟩
  have units i := normalize_unit_fiber O hO P S v hv (C i) (defC i) (y i) (old i)
    (fun j => (pos _ (hy i) j).ne_zero O) (fun _ h => h.2)
  choose B hb iso using units
  exact ⟨_,C,B,defC,disj,cov,fun i => ⟨hb i,iso i⟩⟩

end GeneralizedEuler.Section4
