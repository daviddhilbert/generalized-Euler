module

public import Section4.SliceWeights
public import Section4.ChartRefinement
import all Section4.SliceWeights

/-! Equality of the assigned tensors under a simultaneous value and residue subdivision. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

theorem sum_active_swap {I H T : Type*} [Fintype I] [Fintype H] [AddCommMonoid T]
    (active : I → H → Bool) (f : ∀ i j, active i j = true → T) :
    ∑ i, ∑ j : {j // active i j = true}, f i j.val j.property =
      ∑ j, ∑ i : {i // active i j = true}, f i.val j i.property := by
  let e : (Σ i, {j // active i j = true}) ≃ (Σ j, {i // active i j = true}) :=
    ⟨fun ⟨i,j⟩ => ⟨j.val,i,j.property⟩,fun ⟨j,i⟩ => ⟨i.val,j,i.property⟩,fun _ => rfl,fun _ => rfl⟩
  rw [← Fintype.sum_sigma',← Fintype.sum_sigma']
  exact e.sum_comp (fun p => f p.2.val p.1 p.2.property)

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

include powers resBalance valBalance lang in
theorem tensor_piece_subdivision {l} (p : ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n) (hp : p.measurable O v hO P S) (c : Fin l → DefinablePiece JG G n)
    (active : Fin l → Bool) (unique : ∀ γ, ∃! t, γ ∈ (c t).support)
    (spec : ∀ t γ, γ ∈ (c t).support → (γ ∈ p.value.support ↔ active t = true)) :
    ∃ hd : ∀ t : {t // active t = true}, isRVSet _ S (unitSet O v (residueIndex (c t.val).frame) (p.onSlice (c t.val))),
      Rmap (p.residueWeight O v hv hO P S hp) ⊗ₜ[C] Vmap (pieceClass p.value.domain p.value.definable) =
        ∑ t : {t // active t = true},
          Rmap (unitWeight O v hv hO P S (residueIndex (c t.val).frame) (p.onSlice (c t.val)) (hd t))
            ⊗ₜ[C] Vmap (pieceClass (c t.val).domain (c t.val).definable) := by
  classical
  have parent (t : {t // active t = true}) : (c t.val).support ⊆ p.value.support :=
    fun γ hγ => (spec t.val γ hγ).mpr t.property
  choose hd eq using fun t => chart_slice_weight O v hv hO P powers S p (c t.val) hp (parent t)
  refine ⟨hd,?_⟩
  rw [subdivided_value_class lang p.value c active unique spec,map_sum,TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl; intro t _
  rw [map_mul,map_pow,mul_comm,← valBalance,balance_rank_drop,resBalance,← map_pow,← map_mul,← eq t]

variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
include hs in
theorem chart_column_partition {I : Type} (p : I → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n)
    (disj : Pairwise (fun i j => Disjoint ((p i).carrier s) ((p j).carrier s)))
    (c : DefinablePiece JG G n) (active : I → Bool) [Fintype {i // active i = true}]
    (spec : ∀ i γ, γ ∈ c.support → (γ ∈ (p i).value.support ↔ active i = true))
    (hc : ∀ i : {i // active i = true}, isRVSet _ S (unitSet O v (residueIndex c.frame) ((p i.val).onSlice c)))
    (hd : isRVSet _ S (unitSet O v (residueIndex c.frame) (⋃ i : {i // active i = true}, (p i.val).onSlice c))) :
    unitWeight O v hv hO P S (residueIndex c.frame) (⋃ i : {i // active i = true}, (p i.val).onSlice c) hd =
      ∑ i : {i // active i = true}, unitWeight O v hv hO P S (residueIndex c.frame) ((p i.val).onSlice c) (hc i) := by
  have hdj := ChartPiece.slice_disjoint (F := F) (T := Additive (PositiveRV O)) (v := v)
    (V := Additive O.ValueGroupˣ) (G := G) (J := JG) (n := n) (I := I) s hs p c active spec disj
  exact unit_partition O v hv hO P S (residueIndex c.frame) _ hd
    (fun i : {i // active i = true} => (p i.val).onSlice c) hc hdj rfl

private theorem mapped_sum_tensor {I : Type*} [Fintype I] {A B D E : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring D] [CommSemiring E] [Algebra A D] [Algebra A E]
    (f : B →+* D) (a : I → B) (b : B) (z : E) (h : b = ∑ i, a i) :
    ∑ i, f (a i) ⊗ₜ[A] z = f b ⊗ₜ[A] z := by rw [h,map_sum,TensorProduct.sum_tmul]

set_option maxHeartbeats 1600000 in
include powers resBalance valBalance lang hs in
theorem tensor_family_subdivision {I : Type} [Fintype I] {l} (p : I → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n)
    (hp : ∀ i, (p i).measurable O v hO P S)
    (disj : Pairwise (fun i j => Disjoint ((p i).carrier s) ((p j).carrier s)))
    (c : Fin l → DefinablePiece JG G n) (active : I → Fin l → Bool)
    (unique : ∀ γ, ∃! t, γ ∈ (c t).support)
    (spec : ∀ i t γ, γ ∈ (c t).support → (γ ∈ (p i).value.support ↔ active i t = true)) :
    ∃ hd : ∀ t, isRVSet _ S (unitSet O v (residueIndex (c t).frame)
        (⋃ i : {i // active i t = true}, (p i.val).onSlice (c t))),
      ∑ i, Rmap ((p i).residueWeight O v hv hO P S (hp i)) ⊗ₜ[C] Vmap (pieceClass (p i).value.domain (p i).value.definable) =
        ∑ t, Rmap (unitWeight O v hv hO P S (residueIndex (c t).frame)
          (⋃ i : {i // active i t = true}, (p i.val).onSlice (c t)) (hd t))
          ⊗ₜ[C] Vmap (pieceClass (c t).domain (c t).definable) := by
  classical
  choose each weight using fun i => tensor_piece_subdivision O v hv hO P powers S lang e Rmap Vmap
    resBalance valBalance (p i) (hp i) c (active i) unique (spec i)
  let R t := ⋃ i : {i // active i t = true}, (p i.val).onSlice (c t)
  have hd t : isRVSet _ S (unitSet O v (residueIndex (c t).frame) (R t)) := by
    unfold unitSet R
    rw [Set.image_iUnion]
    exact isRVSet_iUnion (fun i => each i.val ⟨t,i.property⟩)
  refine ⟨hd,?_⟩
  refine (Finset.sum_congr rfl (fun i _ => weight i)).trans ?_
  refine (sum_active_swap active (fun i t h => Rmap (unitWeight O v hv hO P S _ ((p i).onSlice (c t)) (each i ⟨t,h⟩))
    ⊗ₜ[C] Vmap (pieceClass (c t).domain (c t).definable))).trans ?_
  apply Finset.sum_congr rfl; intro t _
  apply mapped_sum_tensor
  exact chart_column_partition O v hv hO P S s hs p disj (c t) (fun i => active i t)
    (fun i => spec i t) (fun i => each i.val ⟨t,i.property⟩) (hd t)

end GeneralizedEuler.Section4
