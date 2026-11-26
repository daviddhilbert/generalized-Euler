module

public import Section4.PositiveValuation
public import Section4.SubframeCarrier
import all Section4.SubframeCarrier
import all Section4.SliceWeights
import all Section4.PositiveValuation
import all Section4.GraphProjectionSums
import all Section4.ValueFrames
import all Section4.PositiveRectangles
import all Section4.ValueStratification
import all Section4.StandardFrame

/-! Rank reduction for a pure rectangle whose value domain need not contain
an independent tuple. This includes products of two value factors. -/
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
local instance rawUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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
theorem arbitrary_rectangle_weight {r n}
    (A : ValueFrame G r n) (D : Set (Fin r → Additive O.ValueGroupˣ)) (hd : (G : Set _).Definable JG D)
    (B : Set (A.dependent → v.ker)) (hb : isRVSet _ S (unitSet O v (residueIndex A) B)) :
    HasChartWeight O v hv hO P S Rmap Vmap s (A.assemblySet (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) (F := F) (v := v) s D B)
      (Rmap (unitWeight O v hv hO P S (residueIndex A) B hb) ⊗ₜ[C] Vmap (pieceClass D hd)) := by
  obtain ⟨l,c,cover,disj,eq⟩ := piece_degree_decomposition lang sat D hd
  let p (i : Fin l) := A.subframeChart (v := v) (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) B (c i)
  have weight (i : Fin l) : ∃ h : (p i).measurable O v hO P S,
      (p i).residueWeight O v hv hO P S h =
        unitWeight O v hv hO P S (residueIndex A) B hb * entireUnitWeight O v hv hO P S 1 ^ (r-(c i).rank) := by
    obtain ⟨α,hα,hi⟩ := (c i).independent
    have hit : (A.comp (c i).frame).eval α ∈ Set.range A.eval := ⟨_,(A.comp_eval (c i).frame α).symm⟩
    exact frame_slice_weight O v hv hO P powers S A (A.comp (c i).frame) B hb α hi hit
  choose hm hw using weight
  have partition := A.subframe_partition (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) (v := v) (J := JG)
    s hs D B c cover disj
  refine ⟨l,p,hm,partition.1,partition.2,?_⟩
  rw [eq,map_sum,TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl; intro i _
  change Rmap ((p i).residueWeight O v hv hO P S (hm i)) ⊗ₜ[C] Vmap (pieceClass (c i).domain (c i).definable) = _
  rw [map_mul,map_pow,mul_comm,← valBalance,balance_rank_drop,resBalance,← map_pow,← map_mul,← hw i]

end GeneralizedEuler.Section4
