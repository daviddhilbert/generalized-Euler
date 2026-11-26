module

public import Section4.ChartTensorWeights
import all Section4.ChartTensorWeights
import all Section4.SliceComparison

/-! Chart sums agree for any two finite disjoint decompositions of the same
positive leading-term set, even when their value projections overlap. -/
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
include powers resBalance valBalance hs lang in
theorem equal_chart_sums {I H : Type} [Fintype I] [Fintype H]
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))
    (p : I → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n)
    (q : H → ChartPiece (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) v G JG n)
    (hp : ∀ i, (p i).measurable O v hO P S) (hq : ∀ j, (q j).measurable O v hO P S)
    (dp : Pairwise (fun i j => Disjoint ((p i).carrier s) ((p j).carrier s)))
    (dq : Pairwise (fun i j => Disjoint ((q i).carrier s) ((q j).carrier s)))
    (cover : (⋃ i, (p i).carrier s) = ⋃ j, (q j).carrier s) :
    ∑ i, Rmap ((p i).residueWeight O v hv hO P S (hp i)) ⊗ₜ[C] Vmap (pieceClass (p i).value.domain (p i).value.definable) =
      ∑ j, Rmap ((q j).residueWeight O v hv hO P S (hq j)) ⊗ₜ[C] Vmap (pieceClass (q j).value.domain (q j).value.definable) := by
  classical
  let sets := Sum.elim (fun i => (p i).value.support) (fun j => (q j).value.support)
  have measurable (i : I ⊕ H) : (G : Set _).Definable JG (sets i) := by
    cases i with
    | inl i => exact support_definable lang (p i).value
    | inr j => exact support_definable lang (q j).value
  obtain ⟨l,c,active,unique,spec⟩ := stratify_memberships lang sat sets measurable
  let ap (i : I) t := active t (.inl i)
  let aq (j : H) t := active t (.inr j)
  obtain ⟨left,leq⟩ := tensor_family_subdivision O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs
    p hp dp c ap unique (fun i t => spec t (.inl i))
  obtain ⟨right,req⟩ := tensor_family_subdivision O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs
    q hq dq c aq unique (fun j t => spec t (.inr j))
  refine leq.trans ((Finset.sum_congr rfl ?_).trans req.symm)
  intro t _
  obtain ⟨α,hα,_⟩ := (c t).independent
  let z := s ∘ α
  have hz : v ∘ z ∈ (c t).domain := by
    have eq : v ∘ z = α := funext fun i => DFunLike.congr_fun hs (α i)
    rwa [eq]
  have spl (i : I) : ∀ γ ∈ (c t).support, γ ∈ (p i).value.support ↔ ap i t = true := spec t (.inl i)
  have spr (j : H) : ∀ γ ∈ (c t).support, γ ∈ (q j).value.support ↔ aq j t = true := spec t (.inr j)
  have ll := @ChartPiece.slice_union F (Additive (PositiveRV O)) (Additive O.ValueGroupˣ)
    _ _ _ _ _ v s hs G JG _ n I p (c t) (fun i => ap i t) spl z hz
  have rr := @ChartPiece.slice_union F (Additive (PositiveRV O)) (Additive O.ValueGroupˣ)
    _ _ _ _ _ v s hs G JG _ n H q (c t) (fun j => aq j t) spr z hz
  rw [cover] at ll
  have eq := unitWeight_congr O v hv hO P S (residueIndex (c t).frame) _ (left t) (ll.trans rr.symm) (right t)
  exact congrArg (fun a => Rmap a ⊗ₜ[C] Vmap (pieceClass (c t).domain (c t).definable)) eq

end GeneralizedEuler.Section4
