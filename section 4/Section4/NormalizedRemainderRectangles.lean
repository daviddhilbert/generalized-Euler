module

public import Section4.HeightDropSharp
public import Section4.RectanglePartitionWeights
import all Section4.NormalRectangles
import all Section4.HeightDropSharp
import all Section4.ResidueProducts
import all Section4.RectangleProducts
import all Section4.RVProducts
import all Section4.ValueFactorMap
import all Section4.ValueDegrees
import all Section4.ValueScissors

/-! Balancing an affine value stratum gives an actual normalized
rectangle, with the same homogeneous degree and the rank of the stratum
as its new height. -/
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
local instance remainderRectangleUnsignedStructure : JG.Structure O.ValueGroupˣ :=
  inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable (lang : ValueLanguage (J := JG) G)
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
variable [Algebra C R] [Algebra C W] (e : C) (Rmap : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R) (Vmap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)
  (resBalance : algebraMap C R e = Rmap (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = Vmap (eValue (J := JG) G))

variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (base : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D → isRVSet _ S (positiveSharp O v D))

include powers hs base pull lang resBalance valBalance in
theorem normalized_remainder_rectangle {k m n : ℕ} (degree : m+n = k) (U : Set (Fin m → v.ker))
    (hu : isRVSet _ S (unitSet O v (Equiv.refl _) U)) (p : DefinablePiece JG G n) :
    ∃ q : NormalRectangle (JG := JG) (G := G) O v hO P S k, q.r = p.rank ∧
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (productSet (unitSet O v (Equiv.refl _) U) (positiveSharp O v p.support)) q.points ∧
      Rmap (unitWeight O v hv hO P S (Equiv.refl _) U hu) ⊗ₜ[C] Vmap (pieceClass p.support (support_definable lang p)) =
        q.tensor hv Rmap Vmap := by
  classical
  let lost := n-p.rank
  let idx : Fin lost ≃ p.frame.dependent := (Fintype.equivFinOfCardEq (complement_count p.frame.free)).symm
  have le := Fintype.card_le_of_injective p.frame.free p.frame.free.injective
  simp only [Fintype.card_fin] at le
  have dim : (m+lost)+p.rank = k := by dsimp [lost]; omega
  let allUnits := (Set.univ : Set (Fin lost → v.ker))
  let first := unitSet O v (Equiv.refl _) U
  let extra := unitSet O v (Equiv.refl _) allUnits
  let free := positiveSharp O v p.domain
  have he := unit_univ_definable O v hv hO P S (Equiv.refl (Fin lost))
  have hf := pull p.definable
  obtain ⟨hp,hprod⟩ := unit_product O v hv hO P S (Equiv.refl _) (Equiv.refl _) U allUnits hu he
  let q : NormalRectangle (JG := JG) (G := G) O v hO P S k :=
    ⟨m+lost,p.rank,dim,packedProduct O v (Equiv.refl _) (Equiv.refl _) U allUnits,p.domain,hp,p.definable⟩
  refine ⟨q,rfl,?_,?_⟩
  · have cut := frame_sharp_equivalent O v hO P powers S lang s hs base pull p idx
    have replace := rv_product_equivalent (rv_reindex_equivalent _ S (Equiv.refl _) _ hu) cut
    have assoc : RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (productSet first (productSet extra free)) (productSet (productSet first extra) free) := by
      have reindex := rv_reindex_equivalent _ S (Equiv.sumAssoc (Fin m) (Fin lost) (Fin p.rank)) _ (rv_product_definable hu (rv_product_definable he hf))
      convert reindex using 2
      ext x
      exact and_assoc
    have pack := rv_product_equivalent (productSet_cartesian hu he) (rv_reindex_equivalent _ S (Equiv.refl _) _ hf)
    have eq := replace.trans (assoc.trans pack)
    change RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier _ (productSet (unitSet O v (Equiv.refl _) (packedProduct O v (Equiv.refl _) (Equiv.refl _) U allUnits)) free)
    rw [packedProduct_code]
    exact eq
  · have power := entireUnitWeight_power O v hv hO P S lost
    change _ = Rmap (unitWeight O v hv hO P S _ _ hp) ⊗ₜ[C] Vmap (pieceClass _ _)
    rw [support_class lang p,hprod,map_mul,map_mul]
    change _ ⊗ₜ[C] (_ * Vmap (eValue G ^ lost)) = (_ * Rmap (entireUnitWeight O v hv hO P S lost)) ⊗ₜ[C] _
    rw [power,map_pow,map_pow,← valBalance,← resBalance,mul_comm (Vmap (pieceClass _ _)),balance_rank_drop]

end GeneralizedEuler.Section4
