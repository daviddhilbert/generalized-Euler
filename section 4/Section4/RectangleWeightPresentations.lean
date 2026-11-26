module

public import Section4.RectangleWeightFamilies
import all Section4.RectangleWeightFamilies
public import Section4.CanonicalObjectWeights
import all Section4.RVScissorRealization
import all Section4.NormalRectangleCover
import all Section4.NormalRectangles
import all Section4.TaggedLiftRealization
import all Section4.RVFamilyOperations
import all Section4.FiniteScissors
import all Section4.ValuePadding
import all Section4.ResidueProducts

/-! Homogeneous rectangle presentations respect the five graded scissor relations. -/
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


namespace RVFamily
variable {L : Language} {E : Type*} {Z : TCsort → Type*} {N : SortedStructure L E Z} {T : SortedSubstructure N}

theorem single_partition {I H : Type} [Finite H] [Fintype I] (D : Set (H → Z .rv)) (hd : isRVSet N T D)
    (a : I → Set (H → Z .rv)) (ha : ∀ i, isRVSet N T (a i))
    (dj : Pairwise fun i j => Disjoint (a i) (a j)) (cover : (⋃ i, a i)=D) :
    cls (single D hd) = ∑ i, cls (single (a i) (ha i)) := by
  subst D
  let b (A : Set (H → Z .rv)) (h : isRVSet N T A) := cls (single A h)
  have empty : isRVSet N T (∅ : Set (H → Z .rv)) := ⟨.falsum,fun _ => Iff.rfl⟩
  exact (finite_scissor_sum b empty ((cls_eq_iff _ _).mpr (single_empty empty rfl))
    (fun h j => h.union j) (fun _ _ h j e => ((cls_eq_iff _ _).mpr (single_cut h j e)).symm)
    a ha dj).choose_spec

end RVFamily

namespace RectangleWeight
local notation "Wt" => RectangleWeight pull hv res val (C := C)

theorem of_cover {I : Type} [Finite I] (D : Set (I → RV0 O)) (hd : isRVSet M S D)
    (cov : HasRectangleCover (JG := JG) (G := G) O v hO P S k D) :
    ∃ t, Wt k (cls (single D hd)) t := by
  obtain ⟨l,a,c,dj,cover,iso⟩ := cov
  let ha i := rv_equivalent_target_definable (iso i).symm
  refine ⟨_,Fin l,inferInstance,c,?_,rfl⟩
  apply Eq.trans (single_partition (N := M) (T := S) D hd a ha dj cover)
  exact Finset.sum_congr rfl fun i _ => (cls_eq_iff _ _).mpr (single_iso _ _ (iso i))

theorem object_presentation
    (covers : ∀ {n} (U : Set (Fin n → RV0 O)), GoodRVSet M S (IsPositiveRV O) U →
      HasRectangleCover (JG := JG) (G := G) O v hO P S n U)
    (minus : rv O (-1) ∈ S.carrier .rv)
    (rvSat : ∀ {n} (D : ℕ → Set (Fin n → RV0 O)), (∀ i, isRVSet M S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (U : RVObject M S k) : ∃ t, Wt k (cls (single U.carrier U.definable)) t := by
  obtain ⟨l,A,B,ha,hb,pos,dj,cv,iso⟩ := positive_object_cover O hO P S U minus rvSat
  choose t ht using fun i => of_cover pull hv res val (C := C) (B i) (hb i) (covers _ ⟨hb i,pos i⟩)
  have eq i := (cls_eq_iff _ _).mpr (single_iso (ha i) (hb i) (iso i))
  rw [single_partition _ U.definable A ha dj cv]
  refine ⟨_,sum pull hv res val _ t (fun i => ?_)⟩
  rw [eq i]; exact ht i

theorem one : Wt 0 1 1 := by
  let D : Set (Fin 0 → Additive O.ValueGroupˣ) := {0}
  have hD : (G : Set _).Definable JG D := zeroTuple_definable G 0
  let b := unit_univ_definable O v hv hO P S (Equiv.refl (Fin 0))
  let z : Rect 0 := ⟨0,0,rfl,Set.univ,D,b,hD⟩
  have unit : unitWeight O v hv hO P S (Equiv.refl (Fin 0)) Set.univ b = 1 :=
    (entireUnitWeight_power O v hv hO P S 0).trans (pow_zero _)
  have val1 : pieceClass D hD = 1 := pieceClass_degree_zero _ _
  have wt : z.tensor hv res val (C := C) = 1 := by
    change res (unitWeight O v hv hO P S _ _ b) ⊗ₜ[C] val (pieceClass D hD) = _
    rw [unit,val1,map_one,map_one]; rfl
  let y : z.points := ⟨Sum.elim (fun i => i.elim0) (fun i => i.elim0),
    ⟨fun i => i.elim0,Set.mem_univ _,Subsingleton.elim _ _⟩,
    fun i => i.elim0,Subsingleton.elim _ _,Subsingleton.elim _ _⟩
  have iso := single_unit (z.points_definable pull) ⟨y.val,Set.eq_singleton_iff_unique_mem.mpr
    ⟨y.property,fun x _ => Subsingleton.elim x y.val⟩⟩
  have h := of_rectangle pull hv res val (C := C) z
  rwa [(cls_eq_iff _ _).mpr iso,wt] at h

end RectangleWeight
end GeneralizedEuler.Section4
