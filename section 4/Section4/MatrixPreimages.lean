module

public import Section4.ResidueProducts
import all Section4.ResidueWeights
import all Section4.DefinableResidueMatrices
import all Section2.RVDefinableEquivalence

public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {I H : Type} [Fintype I] {m n : ℕ} (ei : Fin m ≃ I) (eo : Fin n ≃ H)

local instance unitKernelGroup : AddCommGroup v.ker := @Submodule.addCommGroup F (Additive (PositiveRV O)) _ _ _ v.ker
local instance unitKernelModule : Module F v.ker := @Submodule.module F (Additive (PositiveRV O)) _ _ _ v.ker

include powers hv in
theorem unit_matrix_preimage (A : Matrix H I F) (D : Set (H → v.ker))
    (hd : isRVSet _ S (unitSet O v eo D)) :
    isRVSet _ S (unitSet O v ei (actRows A ⁻¹' D)) := by
  let M := canonicalStructure (L := J) O hO P
  let all := unitSet O v ei Set.univ
  let ex := Equiv.Set.imageOfInjOn (unitTuple O v ei) Set.univ (unitTuple_injective O v ei).injOn
  let f (x : all) := unitTuple O v eo (actRows A (ex.symm x).val)
  have spec (x : I → v.ker) (hx : x ∈ Set.univ) :
      f ⟨unitTuple O v ei x,⟨x,hx,rfl⟩⟩ = unitTuple O v eo (actRows A x) :=
    congrArg (fun t => unitTuple O v eo (actRows A t.val)) (ex.symm_apply_apply ⟨x,hx⟩)
  have graph := unit_matrix_graph O v ei eo A P powers hO S Set.univ (unit_univ_definable O v hv hO P S ei) f spec
  let rel := {w : Fin m ⊕ Fin n → RV0 O | (∃ x : all, x.val = w ∘ Sum.inl ∧ f x = w ∘ Sum.inr) ∧
    w ∘ Sum.inr ∈ unitSet O v eo D}
  have defRel : isRVSet M S rel := graph.inter (isRVSet_precomp Sum.inr hd)
  have eq : {x | ∃ y : Fin n → RV0 O, Sum.elim x y ∈ rel} = unitSet O v ei (actRows A ⁻¹' D) := by
    ext x; constructor
    · rintro ⟨y,⟨z,hx,hy⟩,t,ht,et⟩
      obtain ⟨a,rfl⟩ := ex.surjective z
      have same : t = actRows A a.val := unitTuple_injective O v eo
        (et.trans (hy.symm.trans (spec a.val a.property)))
      exact ⟨a.val,show actRows A a.val ∈ D from same ▸ ht,hx⟩
    · rintro ⟨a,ha,rfl⟩
      let z := ex ⟨a,Set.mem_univ _⟩
      exact ⟨_,⟨z,rfl,spec a (Set.mem_univ _)⟩,_,ha,rfl⟩
  rw [← eq]; exact isRVSet_project defRel

end GeneralizedEuler.Section4
