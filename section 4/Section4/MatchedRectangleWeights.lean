module

public import Section4.MatchedResidueClasses
public import Section4.MatchingSlices
import all Section4.MatchedResidueClasses
import all Section4.MatchedResidueGraphs
import all Section4.ResidueWeights
import all Section4.ValueScissors
import all Section4.MatchingSlices

/-! Both projections of a homogeneous matched slice give the same pure
tensor. The residue comparison is in RES before groupification. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O} {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)}
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)

def residueProjection {m} (U : Set (Fin m → v.ker)) (D : Set (Fin m → Residue O)) :=
  U ∩ (fun u => kernelResidue v ∘ u) ⁻¹' D

include hv hs in
theorem matched_rectangle_tensors {m r : ℕ}
    (q : MatchingSlice (Fin r → Additive O.ValueGroupˣ) (Fin r → Additive O.ValueGroupˣ)
      (Fin m → Residue O) (Fin m → Residue O))
    (dv : (G : Set (Additive O.ValueGroupˣ)).Definable JG (pairedSet q.values))
    (dr : isRVSet _ S (residueGraphCode q.residues))
    (U V : Set (Fin m → v.ker))
    (actual : ∀ u w, (u,w) ∈ q.residues →
      (∃ x ∈ U, kernelResidue v ∘ x = u) ∧ (∃ y ∈ V, kernelResidue v ∘ y = w)) :
    let A := residueProjection U {u | ∃ w, (u,w) ∈ q.residues}
    let B := residueProjection V {w | ∃ u, (u,w) ∈ q.residues}
    ∃ (ha : isRVSet _ S (unitSet O v (Equiv.refl _) A)) (hb : isRVSet _ S (unitSet O v (Equiv.refl _) B)),
      res (unitWeight O v hv hO P S (Equiv.refl _) A ha) ⊗ₜ[C]
          val (pieceClass (Prod.fst '' q.values) (matchedDomain_definable dv)) =
        res (unitWeight O v hv hO P S (Equiv.refl _) B hb) ⊗ₜ[C]
          val (pieceClass (Prod.snd '' q.values) (matchedRange_definable dv)) := by
  dsimp only
  obtain ⟨ha,hb,eq⟩ := matched_residue_classes hv q.residues dr q.residueMap q.residue_graph
    (unitSet_match_projection hv s hs U _ (fun _ ⟨_,h⟩ => (actual _ _ h).1))
    (unitSet_match_projection hv s hs V _ (fun _ ⟨_,h⟩ => (actual _ _ h).2))
  exact ⟨ha,hb,congrArg₂ (fun x y => res x ⊗ₜ[C] val y) eq
    (matched_value_classes dv q.valueMap q.value_graph)⟩

include hv hs in
theorem equal_height_slice_tensors {m n r t : ℕ} (hm : m = n) (hr : r = t)
    (q : MatchingSlice (Fin r → Additive O.ValueGroupˣ) (Fin t → Additive O.ValueGroupˣ)
      (Fin m → Residue O) (Fin n → Residue O))
    (dv : (G : Set (Additive O.ValueGroupˣ)).Definable JG (pairedSet q.values))
    (dr : isRVSet _ S (residueGraphCode q.residues))
    (U : Set (Fin m → v.ker)) (V : Set (Fin n → v.ker))
    (actual : ∀ u w, (u,w) ∈ q.residues →
      (∃ x ∈ U, kernelResidue v ∘ x = u) ∧ (∃ y ∈ V, kernelResidue v ∘ y = w)) :
    let A := residueProjection U {u | ∃ w, (u,w) ∈ q.residues}
    let B := residueProjection V {w | ∃ u, (u,w) ∈ q.residues}
    ∃ (ha : isRVSet _ S (unitSet O v (Equiv.refl _) A)) (hb : isRVSet _ S (unitSet O v (Equiv.refl _) B)),
      res (unitWeight O v hv hO P S (Equiv.refl _) A ha) ⊗ₜ[C]
          val (pieceClass (Prod.fst '' q.values) (matchedDomain_definable dv)) =
        res (unitWeight O v hv hO P S (Equiv.refl _) B hb) ⊗ₜ[C]
          val (pieceClass (Prod.snd '' q.values) (matchedRange_definable dv)) := by
  subst n
  subst t
  exact matched_rectangle_tensors hv s hs res val q dv dr U V actual

end GeneralizedEuler.Section4.NormalRectangle
