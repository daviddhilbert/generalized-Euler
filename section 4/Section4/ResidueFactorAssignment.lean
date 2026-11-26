module

public import Section4.ResidueUnitCover
public import Section4.ResidueAssignmentPartition
import all Section4.ResidueWeights
import all Section4.PositivePresentations
import all Section4.LocalRVMeasure
import all Section4.Objects

/-! Recovery of the entire concrete RES factor of the tensor product,
including arbitrary labels, signs, and zeros in the original carrier. -/
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
local instance residueRecoveryUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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

variable (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))
variable (covers : ∀ {n} (U : Set (Fin n → RV0 O)), GoodRVSet _ S (IsPositiveRV O) U →
  HasRectangleCover (JG := JG) (G := G) O v hO P S n U)

local notation "μ[" n "]" => tensorLocalMeasure (k := n) O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete

variable (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
variable (base : ∀ t : S.carrier .rv, Additive.ofMul (RVValueSection.valueCoordinate t.val) ∈ G)
variable (inv : ∀ {m n} L (R : Set (Fin m ⊕ Fin n → RV0 O)), isRVSet _ S R → ∀ w ∈ R, signedShear v hv s hs G L ∘ w ∈ R)

include witness pull in
theorem positive_residue_assignment {n} (D : Set (Fin n → RV0 O)) (hd : isRVSet _ S D)
    (pos : ∀ x ∈ D, ∀ i, IsPositiveRV O (x i))
    (fin : (positiveObject O hO P S D hd pos).IsResidue _ S (signedLabel O hO)) :
    μ[n].assigned D (Rmap (residueClass _ fin) ⊗ₜ[C] (1 : W)) := by
  let U := positiveObject O hO P S D hd pos
  obtain ⟨_,cells,B,hc,dj,cv,units⟩ := residue_unit_cover O v hv hO P S @witness D hd pos fin
  choose hb iso using units
  let obj i := unitObject O v hO P S (Equiv.refl _) (B i) (hb i)
  let hr i := unitObject_residue O v hv hO P S (Equiv.refl _) (B i) (hb i)
  apply assigned_residue_partition μ[n] ((Algebra.TensorProduct.includeLeft : R →ₐ[C] R ⊗[C] W).toRingHom.comp Rmap) U fin cells hc dj cv obj hr iso
  intro i
  exact positive_unit_assignment O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete @pull _ (hb i)

variable (minus : rv O (-1) ∈ S.carrier .rv)
  (rvSat : ∀ {n} (D : ℕ → Set (Fin n → RV0 O)), (∀ i, isRVSet _ S (D i)) → Antitone D →
    (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)

include witness pull base inv minus rvSat in
theorem residue_factor_assignment {n} (U : RVObject _ S n) (hu : U.IsResidue _ S (signedLabel O hO)) :
    μ[n].assigned U.carrier (Rmap (residueClass U hu) ⊗ₜ[C] (1 : W)) := by
  obtain ⟨_,D,E,hd,he,pos,disj,cv,iso⟩ := positive_object_cover O hO P S U minus rvSat
  let V i := positiveObject O hO P S (E i) (he i) (pos i)
  have fin i : (V i).IsResidue _ S (signedLabel O hO) := by
    have sub : D i ⊆ U.carrier := by rw [← cv]; exact Set.subset_iUnion D i
    have src : (Set.range fun x : D i => signedLabel O hO ∘ x.val).Finite :=
      hu.subset (fun _ ⟨x,eq⟩ => ⟨⟨x.val,sub x.property⟩,eq⟩)
    exact positive_residue_image O v hv s hs G hO P S @witness base (D i) (E i) (hd i) src (pos i) (iso i)
      (complete _ (he i) (pos i)) inv
  apply assigned_residue_partition μ[n] ((Algebra.TensorProduct.includeLeft : R →ₐ[C] R ⊗[C] W).toRingHom.comp Rmap) U hu D hd disj cv V fin iso
  intro i
  exact positive_residue_assignment O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete
    @pull @witness (E i) (he i) (pos i) (fin i)

end GeneralizedEuler.Section4
