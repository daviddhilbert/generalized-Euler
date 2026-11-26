module

public import Section4.GraphChartBasis
import all Section4.ProjectedPieceWeights
import all Section4.ProjectedValuePiece
import all Section4.GraphChartBasis
import all Section4.SliceWeights
import all Section4.SliceComparison
import all Section4.ProjectedRVChart

/-! Equality of the two projected tensors of a nonempty injectively
projected graph piece. Both residue classes use projection degree k−r. -/
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
  (lang : ValueLanguage (J := JG) G)
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
variable [Algebra C R] [Algebra C W] (e : C) (Rmap : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R) (Vmap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)
  (resBalance : algebraMap C R e = Rmap (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = Vmap (eValue (J := JG) G))

variable {n : ℕ}


variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable {k : ℕ} (a : ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n)
  (p q : Fin k → Fin n)

set_option maxHeartbeats 800000 in
include hs powers lang in
theorem graph_piece_tensors (ha : a.measurable O v hO P S) (hb : a.residue.Nonempty)
    (ip : Set.InjOn (fun x : Fin n → Additive (PositiveRV O) => x ∘ p) (a.carrier s))
    (iq : Set.InjOn (fun x : Fin n → Additive (PositiveRV O) => x ∘ q) (a.carrier s)) :
    ∃ (b c : ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG k)
      (hm : b.measurable O v hO P S) (hm' : c.measurable O v hO P S),
      b.carrier s = (fun x : Fin n → Additive (PositiveRV O) => x ∘ p) '' a.carrier s ∧
      c.carrier s = (fun x : Fin n → Additive (PositiveRV O) => x ∘ q) '' a.carrier s ∧
      Rmap (b.residueWeight O v hv hO P S hm) ⊗ₜ[C] Vmap (pieceClass b.value.domain b.value.definable) =
        Rmap (c.residueWeight O v hv hO P S hm') ⊗ₜ[C] Vmap (pieceClass c.value.domain c.value.definable) := by
  obtain ⟨d,hd⟩ := positive_kernel_nonzero O hO v hv
  obtain ⟨L⟩ := graph_chart_basis (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) (v := v) (G := G) (J := JG) s hs a p d hd hb ip
  obtain ⟨R'⟩ := graph_chart_basis (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) (v := v) (G := G) (J := JG) s hs a q d hd hb iq
  have il := ProjectionBasis.residue_injection (v := v) (a := a) (T := Additive (PositiveRV O)) (s := s) hs L ip
  have ir := ProjectionBasis.residue_injection (v := v) (a := a) (T := Additive (PositiveRV O)) (s := s) hs R' iq
  obtain ⟨hl,hr,eq⟩ := L.projected_residue_class O v hv hO P powers S R' a.residue ha il ir
  let b := @ProjectionBasis.imageChart F (Additive (PositiveRV O)) (Additive O.ValueGroupˣ) _ _ _ _ _ v G JG _ n k a p L lang
  let c := @ProjectionBasis.imageChart F (Additive (PositiveRV O)) (Additive O.ValueGroupˣ) _ _ _ _ _ v G JG _ n k a q R' lang
  have bm : b.measurable O v hO P S := hl
  have cm : c.measurable O v hO P S := hr
  have ble := @ProjectionBasis.imageChart_carrier F (Additive (PositiveRV O)) (Additive O.ValueGroupˣ) _ _ _ _ _ v s hs G JG _ n k a p L lang
  have cle := @ProjectionBasis.imageChart_carrier F (Additive (PositiveRV O)) (Additive O.ValueGroupˣ) _ _ _ _ _ v s hs G JG _ n k a q R' lang
  refine ⟨b,c,bm,cm,ble,cle,?_⟩
  have req : b.residueWeight O v hv hO P S bm = c.residueWeight O v hv hO P S cm := eq
  have veq : pieceClass b.value.domain b.value.definable = pieceClass c.value.domain c.value.definable :=
    (L.forward_class lang a.value.domain a.value.definable).trans (R'.forward_class lang a.value.domain a.value.definable).symm
  exact congrArg₂ (fun x y => Rmap x ⊗ₜ[C] Vmap y) req veq

end GeneralizedEuler.Section4
