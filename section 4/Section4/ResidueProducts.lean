module

public import Section4.ResidueWeights
import all Section4.ResidueWeights
import all Section4.PositivePresentations
import all Section4.ValueScissors
import all Section4.Scissors
import all Section4.FiniteScissors
import all Section4.DefinableResidueMatrices
import all Section4.ValueFactorMap

/-! Scissors, products and unrestricted coordinates for the residue class of a chart. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {I H : Type} {m r : ℕ} (ei : Fin m ≃ I) (ej : Fin r ≃ H)

theorem unit_partition {B : Type} [Fintype B] (D : Set (I → v.ker)) (hd : isRVSet _ S (unitSet O v ei D))
    (C : B → Set (I → v.ker)) (hc : ∀ j, isRVSet _ S (unitSet O v ei (C j)))
    (disj : Pairwise (fun i j => Disjoint (C i) (C j))) (cover : ⋃ j, C j = D) :
    unitWeight O v hv hO P S ei D hd = ∑ j, unitWeight O v hv hO P S ei (C j) (hc j) := by
  let U := unitObject O v hO P S ei D hd
  let cells i := unitSet O v ei (C i)
  have hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j)) := by
    intro i j h
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,eq⟩
    exact Set.disjoint_left.mp (disj h) hx (unitTuple_injective O v ei eq ▸ hy)
  have hcover : ⋃ i, cells i = U.carrier := by
    change (⋃ i, unitTuple O v ei '' C i) = unitTuple O v ei '' D
    rw [← Set.image_iUnion,cover]
  have cut := residue_class_partition U (unitObject_residue O v hv hO P S ei D hd) cells hc hdisj hcover
  exact cut.trans (Finset.sum_congr rfl fun i _ => residue_class_iso _ _ _ _
    ⟨Equiv.refl _,definable_identity_label _ S (hc i)⟩)

def packedProduct (D : Set (I → v.ker)) (B : Set (H → v.ker)) : Set (Fin (m+r) → v.ker) :=
  {x | x ∘ finSumFinEquiv ∘ Sum.inl ∘ ei.symm ∈ D ∧ x ∘ finSumFinEquiv ∘ Sum.inr ∘ ej.symm ∈ B}

theorem packedProduct_code (D : Set (I → v.ker)) (B : Set (H → v.ker)) :
    unitSet O v (Equiv.refl _) (packedProduct O v ei ej D B) = cartesian (unitSet O v ei D) (unitSet O v ej B) := by
  ext x
  constructor
  · rintro ⟨z,⟨hd,hb⟩,rfl⟩
    exact ⟨⟨_,hd,funext fun i => by simp [Function.comp_def,unitTuple,codeTuple]⟩,
      _,hb,funext fun j => by simp [Function.comp_def,unitTuple,codeTuple]⟩
  · rintro ⟨⟨z,hz,eqz⟩,⟨w,hw,eqw⟩⟩
    let t := Sum.elim (z ∘ ei) (w ∘ ej) ∘ finSumFinEquiv.symm
    refine ⟨t,⟨?_,?_⟩,?_⟩
    · simpa [t,Function.comp_def] using hz
    · simpa [t,Function.comp_def] using hw
    · funext i; obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
      cases j with
      | inl j => simpa [t,unitTuple,codeTuple] using congrFun eqz j
      | inr j => simpa [t,unitTuple,codeTuple] using congrFun eqw j

theorem unit_product (D : Set (I → v.ker)) (B : Set (H → v.ker))
    (hd : isRVSet _ S (unitSet O v ei D)) (hb : isRVSet _ S (unitSet O v ej B)) :
    ∃ hp : isRVSet _ S (unitSet O v (Equiv.refl _) (packedProduct O v ei ej D B)),
      unitWeight O v hv hO P S (Equiv.refl _) _ hp =
        unitWeight O v hv hO P S ei D hd * unitWeight O v hv hO P S ej B hb := by
  let prod := productSet (unitSet O v ei D) (unitSet O v ej B)
  have defProd : isRVSet _ S prod := (isRVSet_precomp Sum.inl hd).inter (isRVSet_precomp Sum.inr hb)
  have eqv := rv_reindex_equivalent _ S finSumFinEquiv.symm prod defProd
  have eq : {y | y ∘ finSumFinEquiv ∈ prod} = unitSet O v (Equiv.refl _) (packedProduct O v ei ej D B) :=
    (packedProduct_code O v ei ej D B).symm
  rw [show finSumFinEquiv.symm.symm = (finSumFinEquiv : Fin m ⊕ Fin r ≃ Fin (m+r)) from rfl,eq] at eqv
  exact ⟨rv_equivalent_target_definable eqv,residue_class_product _ _ _ _ _ _ eqv⟩

def entireUnitWeight (n : ℕ) := unitWeight O v hv hO P S (Equiv.refl (Fin n)) Set.univ
  (unit_univ_definable O v hv hO P S (Equiv.refl _))

theorem entireUnitWeight_power (n : ℕ) : entireUnitWeight O v hv hO P S n = entireUnitWeight O v hv hO P S 1 ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    apply Quotient.sound
    apply RingConGen.Rel.of
    unfold residueRelation
    simp only [MvPolynomial.rename_X,map_one]
    apply RVRelation.one
    refine ⟨fun j : Fin 0 => j.elim0,Set.ext fun x => ?_⟩
    change (∃ t : Fin 0 → v.ker, t ∈ Set.univ ∧ _ = x) ↔ x = _
    constructor
    · intro _; exact funext (fun j : Fin 0 => j.elim0)
    · intro _; exact ⟨fun j => j.elim0,Set.mem_univ _,funext (fun j => j.elim0)⟩
  | succ n ih =>
    obtain ⟨hp,eq⟩ := unit_product O v hv hO P S (Equiv.refl (Fin n)) (Equiv.refl (Fin 1)) Set.univ Set.univ
      (unit_univ_definable O v hv hO P S _) (unit_univ_definable O v hv hO P S _)
    rw [pow_succ,← ih]
    refine Eq.trans ?_ eq
    apply unitWeight_congr
    ext; simp [packedProduct]

end GeneralizedEuler.Section4
