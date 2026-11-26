module

public import Section4.RectangleHeightDescent
public import Section4.ResidueFactorAssignment
import all Section4.ResidueWeights
import all Section4.ResidueScissors
import all Section4.EmptyProductCoordinates
import all Section4.PositivePresentations
import all Section4.FixedResidueImages
public import Section4.CanonicalObjectWeights
import all Section4.RVScissorRealization
import all Section4.NormalRectangleCover
import all Section4.NormalRectangles
import all Section4.TaggedLiftRealization
import all Section4.RVFamilyOperations
import all Section4.FiniteScissors
import all Section4.ValuePadding
import all Section4.ResidueProducts

/-! Recovery of the two factors from rectangle presentations. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k : ℕ}
variable (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
open scoped TensorProduct
open ValueObject
variable {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)


local notation "M" => canonicalStructure (L := J) O hO P
local notation "Rect" => NormalRectangle (JG := JG) (G := G) O v hO P S
open RVFamily



namespace RectangleWeight
local notation "Wt" => RectangleWeight pull hv res val (C := C)

theorem transfer {I H : Type} [Finite I] [Finite H] {D : Set (I → RV0 O)} {E : Set (H → RV0 O)}
    (hd : isRVSet M S D) (he : isRVSet M S E) (iso : RVDefinablyEquivalent M S.carrier D E)
    {x} (h : Wt k (cls (single E he)) x) : Wt k (cls (single D hd)) x := by
  rwa [(cls_eq_iff _ _).mpr (single_iso hd he iso)]

theorem sharp {r} (D : Set (Fin r → Additive O.ValueGroupˣ)) (hd : (G : Set _).Definable JG D) :
    Wt r (cls (single (positiveSharp O v D) (pull hd))) ((1 : R) ⊗ₜ[C] val (pieceClass D hd)) := by
  let hu := unit_univ_definable O v hv hO P S (Equiv.refl (Fin 0))
  let z : NormalRectangle (JG := JG) (G := G) O v hO P S r := ⟨0,r,Nat.zero_add _,Set.univ,D,hu,hd⟩
  have unit : unitWeight O v hv hO P S (Equiv.refl (Fin 0)) Set.univ hu = 1 :=
    (entireUnitWeight_power O v hv hO P S 0).trans (pow_zero _)
  have wt : z.tensor hv res val (C := C) = 1 ⊗ₜ[C] val (pieceClass D hd) := by
    change res (unitWeight O v hv hO P S _ _ hu) ⊗ₜ[C] _ = _
    rw [unit,map_one]
  have model := of_rectangle pull hv res val (C := C) z
  rw [wt] at model
  have left : unitSet O v (Equiv.refl (Fin 0)) Set.univ = Set.univ :=
    Set.eq_univ_iff_forall.mpr (fun _ => ⟨fun i => i.elim0,Set.mem_univ _,Subsingleton.elim _ _⟩)
  apply transfer pull hv res val _ _ _ model
  change RVDefinablyEquivalent _ S.carrier _ (productSet (unitSet O v (Equiv.refl (Fin 0)) _) (positiveSharp O v D))
  rw [left]; exact rv_empty_product_left (pull hd)

theorem unit {m} (B : Set (Fin m → v.ker)) (hb : isRVSet _ S (unitSet O v (Equiv.refl _) B)) :
    Wt m (cls (single (unitSet O v (Equiv.refl _) B) hb)) (res (unitWeight O v hv hO P S (Equiv.refl _) B hb) ⊗ₜ[C] (1 : W)) := by
  let D : Set (Fin 0 → Additive O.ValueGroupˣ) := {0}
  have hd : (G : Set _).Definable JG D := zeroTuple_definable G 0
  let z : NormalRectangle (JG := JG) (G := G) O v hO P S m := ⟨m,0,rfl,B,D,hb,hd⟩
  have val1 : pieceClass D hd = 1 := pieceClass_degree_zero _ _
  have wt : z.tensor hv res val (C := C) = res (unitWeight O v hv hO P S _ _ hb) ⊗ₜ[C] (1 : W) := by
    change _ ⊗ₜ[C] val (pieceClass D hd) = _
    rw [val1,map_one]
  have model := of_rectangle pull hv res val (C := C) z
  rw [wt] at model
  have right : positiveSharp O v D = Set.univ := Set.eq_univ_iff_forall.mpr
    (fun _ => ⟨fun i => i.elim0,Subsingleton.elim _ _,Subsingleton.elim _ _⟩)
  apply transfer pull hv res val _ _ _ model
  change RVDefinablyEquivalent _ S.carrier _ (productSet _ (positiveSharp O v D))
  rw [right]; exact rv_empty_product_right hb


theorem residue_partition (w : ResidueSemiring M S (signedLabel O hO) →+* TensorProduct C R W)
    (U : RVObject M S k) (hu : U.IsResidue M S (signedLabel O hO)) {I : Type} [Fintype I]
    (D : I → Set (Fin U.arity → RV0 O)) (hd : ∀ i, isRVSet M S (D i))
    (dj : Pairwise (fun i j => Disjoint (D i) (D j))) (cv : (⋃ i, D i) = U.carrier)
    (B : I → RVObject M S k) (hb : ∀ i, (B i).IsResidue M S (signedLabel O hO))
    (iso : ∀ i, RVDefinablyEquivalent M S.carrier (D i) (B i).carrier)
    (hw : ∀ i, Wt k (cls (single (B i).carrier (B i).definable)) (w (residueClass (B i) (hb i)))) :
    Wt k (cls (single U.carrier U.definable)) (w (residueClass U hu)) := by
  have eq : residueClass U hu = ∑ i, residueClass (B i) (hb i) := (residue_class_partition U hu D hd dj cv).trans
    (Finset.sum_congr rfl fun i _ => residue_class_iso _ _ _ _ (iso i))
  rw [eq,map_sum,single_partition U.carrier U.definable D hd dj cv]
  exact sum pull hv res val _ _ fun i => transfer pull hv res val _ _ (iso i) (hw i)

local instance heightFactorUnsignedStructure : JG.Structure O.ValueGroupˣ := inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (complete : ∀ {n} (U : Set (Fin n → RV0 O)), isRVSet (canonicalStructure (L := J) O hO P) S U → (∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) →
    AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' U))
variable (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
variable (base : ∀ t : S.carrier .rv, Additive.ofMul (RVValueSection.valueCoordinate t.val) ∈ G)
variable (inv : ∀ {m n} L (R : Set (Fin m ⊕ Fin n → RV0 O)), isRVSet _ S R → ∀ w ∈ R, signedShear v hv s hs G L ∘ w ∈ R)

include witness in
theorem positive_residue {n} (D : Set (Fin n → RV0 O)) (hd : isRVSet _ S D)
    (pos : ∀ x ∈ D, ∀ i, IsPositiveRV O (x i))
    (fin : (positiveObject O hO P S D hd pos).IsResidue _ S (signedLabel O hO)) :
    Wt n (cls (single D hd)) (res (residueClass _ fin) ⊗ₜ[C] (1 : W)) := by
  let U := positiveObject O hO P S D hd pos
  obtain ⟨_,cells,B,hc,dj,cv,units⟩ := residue_unit_cover O v hv hO P S @witness D hd pos fin
  choose hb iso using units
  let obj i := unitObject O v hO P S (Equiv.refl _) (B i) (hb i)
  let hr i := unitObject_residue O v hv hO P S (Equiv.refl _) (B i) (hb i)
  apply residue_partition pull hv res val ((Algebra.TensorProduct.includeLeft : R →ₐ[C] R ⊗[C] W).toRingHom.comp res) U fin cells hc dj cv obj hr iso
  intro i
  exact unit pull hv res val _ (hb i)

variable (minus : rv O (-1) ∈ S.carrier .rv)
  (rvSat : ∀ {n} (D : ℕ → Set (Fin n → RV0 O)), (∀ i, isRVSet _ S (D i)) → Antitone D →
    (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)

include witness base inv minus rvSat complete in
theorem residue {n} (U : RVObject _ S n) (hu : U.IsResidue _ S (signedLabel O hO)) :
    Wt n (cls (single U.carrier U.definable)) (res (residueClass U hu) ⊗ₜ[C] (1 : W)) := by
  obtain ⟨_,D,E,hd,he,pos,disj,cv,iso⟩ := positive_object_cover O hO P S U minus rvSat
  let V i := positiveObject O hO P S (E i) (he i) (pos i)
  have fin i : (V i).IsResidue _ S (signedLabel O hO) := by
    have sub : D i ⊆ U.carrier := by rw [← cv]; exact Set.subset_iUnion D i
    have src : (Set.range fun x : D i => signedLabel O hO ∘ x.val).Finite :=
      hu.subset (fun _ ⟨x,eq⟩ => ⟨⟨x.val,sub x.property⟩,eq⟩)
    exact positive_residue_image O v hv s hs G hO P S @witness base (D i) (E i) (hd i) src (pos i) (iso i)
      (complete _ (he i) (pos i)) inv
  apply residue_partition pull hv res val ((Algebra.TensorProduct.includeLeft : R →ₐ[C] R ⊗[C] W).toRingHom.comp res) U hu D hd disj cv V fin iso
  intro i
  exact positive_residue pull hv res val @witness (E i) (he i) (pos i) (fin i)

end RectangleWeight
end GeneralizedEuler.Section4
