module

public import Section4.StandardRectangleWeight
public import Section4.PositiveAdditivity
import all Section4.PositiveValuation
import all Section4.StandardRectangleWeight
import all Section4.ValueScissors
import all Section4.ResidueWeights
import all Section4.ValueFrames

/-! Additivity on partitions of a rectangle in its residue and value
labels. The proof only uses chart weights on the same underlying set
and finite scissors. -/
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
local instance partitionUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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
include powers hs valBalance resBalance lang sat in
theorem rectangle_partition_tensors {m r : ℕ} {I : Type} [Fintype I]
    (U : Set (Fin m → v.ker)) (D : Set (Fin r → Additive O.ValueGroupˣ))
    (hu : isRVSet _ S (unitSet O v (Equiv.refl _) U)) (hd : (G : Set _).Definable JG D)
    (A : I → Set (Fin m → v.ker)) (B : I → Set (Fin r → Additive O.ValueGroupˣ))
    (ha : ∀ i, isRVSet _ S (unitSet O v (Equiv.refl _) (A i))) (hb : ∀ i, (G : Set _).Definable JG (B i))
    (disj : Pairwise (fun i j => Disjoint (A i ×ˢ B i) (A j ×ˢ B j)))
    (cover : (⋃ i, A i ×ˢ B i) = U ×ˢ D) :
    Rmap (unitWeight O v hv hO P S (Equiv.refl _) U hu) ⊗ₜ[C] Vmap (pieceClass D hd) =
      ∑ i, Rmap (unitWeight O v hv hO P S (Equiv.refl _) (A i) (ha i)) ⊗ₜ[C] Vmap (pieceClass (B i) (hb i)) := by
  let cloud (Y : Set ((Fin m → v.ker) × (Fin r → Additive O.ValueGroupˣ))) :=
    {x : Fin (m+r) → Additive (PositiveRV O) | ∃ u, v.ker.subtype ∘ u = x ∘ stdLeft m r ∧
      (u,v ∘ x ∘ stdRight m r) ∈ Y}
  have rect (A : Set (Fin m → v.ker)) (B : Set (Fin r → Additive O.ValueGroupˣ)) :
      cloud (A ×ˢ B) = cartesian ((fun u : Fin m → v.ker => v.ker.subtype ∘ u) '' A) {z | v ∘ z ∈ B} := by
    ext x
    exact ⟨fun ⟨u,eq,h₁,h₂⟩ => ⟨⟨u,h₁,eq⟩,h₂⟩,fun ⟨⟨u,h₁,eq⟩,h₂⟩ => ⟨u,eq,h₁,h₂⟩⟩
  have cv : (⋃ i, cloud (A i ×ˢ B i)) = cloud (U ×ˢ D) := by
    rw [← cover]
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i,u,eq,h⟩ => ⟨u,eq,Set.mem_iUnion.mpr ⟨i,h⟩⟩,fun ⟨u,eq,h⟩ => by
      obtain ⟨i,h⟩ := Set.mem_iUnion.mp h; exact ⟨i,u,eq,h⟩⟩
  have dj : Pairwise (fun i j => Disjoint (cloud (A i ×ˢ B i)) (cloud (A j ×ˢ B j))) := by
    intro i j ne
    apply Set.disjoint_left.mpr
    rintro x ⟨u,he,h⟩ ⟨w,he',h'⟩
    obtain rfl : u = w := funext fun t => Subtype.ext (congrFun (he.trans he'.symm) t)
    exact Set.disjoint_left.mp (disj ne) h h'
  have whole := standard_rectangle_weight O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat D hd U hu
  have each i := standard_rectangle_weight O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat
    (B i) (hb i) (A i) (ha i)
  apply single_chart_weight O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat whole
  rw [← rect,← cv]
  exact finiteChartWeight_partition _ _ _ _ _ dj (fun i => (rect _ _).symm ▸ each i)

end GeneralizedEuler.Section4
