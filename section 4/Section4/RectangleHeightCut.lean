module

public import Section4.NormalizedRemainderRectangles
public import Section4.Subrectangles
public import Section4.RectangleRemainderGrid
import all Section4.NormalRectangles
import all Section4.Subrectangles
import all Section4.ValueStratification
import all Section4.ValueFrames
import all Section4.ValueScissors

/-! Split one summand along the disjoint matched labels. The original
tensor is the sum of the matched tensors and the tensors of a residual
family of smaller height. Each change of coordinates on the residual
family is a fixed-base RV bijection. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
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
local instance heightCutUnsignedStructure : JG.Structure O.ValueGroupˣ :=
  inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (lang : ValueLanguage (J := JG) G)
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
variable [Algebra C R] [Algebra C W] (e : C) (Rmap : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R) (Vmap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)
  (resBalance : algebraMap C R e = Rmap (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = Vmap (eValue (J := JG) G))

variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (base : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D → isRVSet _ S (positiveSharp O v D))

variable (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))

include powers hs base pull lang resBalance valBalance sat in
theorem cut_to_lower_height {k : ℕ} (c : NormalRectangle (JG := JG) (G := G) O v hO P S k)
    {I : Type} [Fintype I] (a : I → Subrectangle c)
    (dj : Pairwise (fun i j => Disjoint (a i).labels (a j).labels))
    (height : ℕ) (bound : c.r ≤ height)
    (covered : c.r = height → ∀ u ∈ c.units, ∀ x ∈ c.values, LinearIndependent F (G.mkQ ∘ x) →
      ∃ i, (u,x) ∈ (a i).labels) :
    ∃ (l : ℕ) (rest : Fin l → Subrectangle c)
      (normal : Fin l → NormalRectangle (JG := JG) (G := G) O v hO P S k),
      (∀ t, (normal t).r < height ∧ RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (rest t).points (normal t).points) ∧
      Pairwise (fun i j => Disjoint (rest i).labels (rest j).labels) ∧
      (c.units ×ˢ c.values) \ (⋃ i, (a i).labels) = ⋃ t, (rest t).labels ∧
      c.tensor hv Rmap Vmap (C := C) = (∑ i, (a i).rect.tensor hv Rmap Vmap) +
        ∑ t, (normal t).tensor hv Rmap Vmap := by
  classical
  obtain ⟨l,p,R,prop,distinct,rem⟩ := rectangle_remainder_grid (P := fun U => isRVSet _ S (unitSet O v (Equiv.refl _) U)) lang sat c.units c.values c.valuesDef
    (fun i => (a i).units) (fun i => (a i).values) (fun i => (a i).valuesDef)
    (residue_remainder_definable c a) height bound covered
  have contains (t : Fin l) : R t ×ˢ (p t).support ⊆ c.units ×ˢ c.values :=
    fun z hz => ((congrArg (z ∈ ·) rem).mpr (Set.mem_iUnion.mpr ⟨t,hz⟩)).1
  have nz (t) : (p t).support.Nonempty := by
    obtain ⟨x,h,_⟩ := (p t).independent
    exact ⟨_,x,h,rfl⟩
  let b (t : Fin l) : Subrectangle c := ⟨R t,(p t).support,(prop t).1,support_definable lang _,
    fun u h => (@contains t (u,(nz t).choose) ⟨h,(nz t).choose_spec⟩).1,
    fun x h => (@contains t ((prop t).2.1.choose,x) ⟨(prop t).2.1.choose_spec,h⟩).2⟩
  have chooseNormal (t : Fin l) := normalized_remainder_rectangle O v hv hO P powers S lang e Rmap Vmap
    resBalance valBalance s hs base pull c.degree (R t) (prop t).1 (p t)
  choose q rank iso weight using chooseNormal
  have bdj : Pairwise (fun i j => Disjoint (b i).labels (b j).labels) :=
    fun i j ne => Set.disjoint_left.mpr fun _ h h' => Set.disjoint_left.mp (distinct ne) h.2 h'.2
  refine ⟨l,b,q,fun t => ⟨(rank t).trans_lt (prop t).2.2,iso t⟩,bdj,rem,?_⟩
  let z : I ⊕ Fin l → Subrectangle c := Sum.elim a b
  have cross (i t) : Disjoint (a i).labels (b t).labels := by
    apply Set.disjoint_left.mpr
    intro x h h'
    exact ((congrArg (x ∈ ·) rem).mpr (Set.mem_iUnion.mpr ⟨t,h'⟩)).2 (Set.mem_iUnion.mpr ⟨i,h⟩)
  have disj : Pairwise (fun i j => Disjoint (z i).labels (z j).labels) := by
    rintro (i|i) (j|j) ne
    · exact dj (fun eq => ne (congrArg Sum.inl eq))
    · exact cross i j
    · exact (cross j i).symm
    · exact bdj (fun eq => ne (congrArg Sum.inr eq))
  have cover : (⋃ t, (z t).labels) = c.units ×ˢ c.values := by
    rw [Set.iUnion_sum]
    change (⋃ i, (a i).labels) ∪ (⋃ t, (b t).labels) = _
    rw [show (⋃ t, (b t).labels) = _ from rem.symm]
    exact Set.union_sdiff_cancel (Set.iUnion_subset fun i x h => ⟨(a i).unitsSub h.1,(a i).valuesSub h.2⟩)
  have sum := rectangle_partition_tensors O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat
    c.units c.values c.unitsDef c.valuesDef (fun t => (z t).units) (fun t => (z t).values)
    (fun t => (z t).unitsDef) (fun t => (z t).valuesDef) disj cover
  change c.tensor hv Rmap Vmap (C := C) = ∑ t, (z t).rect.tensor hv Rmap Vmap at sum
  rw [sum,Fintype.sum_sum_type]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun t _ => weight t)

end GeneralizedEuler.Section4.NormalRectangle
