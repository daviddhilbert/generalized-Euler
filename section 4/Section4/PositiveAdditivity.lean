module

public import Section4.PositiveValuation
public import Section4.CombinePartitions
import all Section4.PositiveValuation
import all Section4.CanonicalChartCover
import all Section4.GraphProjectionSums
import all Section4.SliceWeights

/-! Finite additivity and the unique positive-set valuation used before
extending to tagged objects. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

theorem finiteChartWeight_partition {A X T : Type*} [AddCommMonoid T] (carrier : A → Set X)
    (meas : A → Prop) (weight : ∀ a, meas a → T) {I : Type} [Fintype I]
    (D : I → Set X) (w : I → T) (disj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (each : ∀ i, finiteChartWeight carrier meas weight (D i) (w i)) :
    finiteChartWeight carrier meas weight (⋃ i, D i) (∑ i, w i) := by
  let B := {a // meas a}
  let get (a : B) := carrier a.val
  let val (a : B) := weight a.val a.property
  have cells i : ∃ (n : ℕ) (a : Fin n → B), Pairwise (fun j k => Disjoint (get (a j)) (get (a k))) ∧
      (⋃ j, get (a j)) = D i ∧ (∑ j, val (a j)) = w i := by
    obtain ⟨l,p,hp,d,c,h⟩ := each i
    exact ⟨l,fun j => ⟨p j,hp j⟩,d,c,h⟩
  obtain ⟨n,a,hd,hc,hw⟩ := combine_partitions get val D disj w cells
  exact ⟨n,fun i => (a i).val,fun i => (a i).property,hd,hc,hw⟩

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] {G : Submodule F (Additive O.ValueGroupˣ)}
local instance additiveWeightUnsignedStructure : JG.Structure O.ValueGroupˣ :=
  inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable  (lang : ValueLanguage (J := JG) G)
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
variable [Algebra C R] [Algebra C W] (e : C) (Rmap : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R) (Vmap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)
  (resBalance : algebraMap C R e = Rmap (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = Vmap (eValue (J := JG) G))

variable {n : ℕ}


variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)


variable {k : ℕ}

variable (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))
variable (complete : ∀ {n} (U : Set (Fin n → RV0 O)), isRVSet _ S U → (∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) →
  AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' U))


def positiveSetWeight (D : Set (Fin k → RV0 O)) (hd : isRVSet _ S D) (pd : ∀ x ∈ D, ∀ i, IsPositiveRV O (x i))
    (covers : ∀ {n} (U : Set (Fin n → RV0 O)), isRVSet _ S U → (∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) →
      AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' U)) : TensorProduct C R W :=
  (chart_weight_exists O v hv hO P S Rmap Vmap (C := C) s (covers D hd pd)).choose

theorem positiveSetWeight_spec (D : Set (Fin k → RV0 O)) (hd : isRVSet _ S D) (pd : ∀ x ∈ D, ∀ i, IsPositiveRV O (x i)) :
    HasChartWeight O v hv hO P S Rmap Vmap s (codeTuple O ⁻¹' D)
      (positiveSetWeight O v hv hO P S Rmap Vmap (C := C) s D hd pd complete) :=
  (chart_weight_exists O v hv hO P S Rmap Vmap (C := C) s (complete D hd pd)).choose_spec

include hs powers lang resBalance valBalance sat in
theorem positiveSetWeight_partition {I : Type} [Fintype I] (D : Set (Fin k → RV0 O)) (hd : isRVSet _ S D)
    (pd : ∀ x ∈ D, ∀ i, IsPositiveRV O (x i)) (B : I → Set (Fin k → RV0 O))
    (hb : ∀ i, isRVSet _ S (B i)) (pb : ∀ i x, x ∈ B i → ∀ j, IsPositiveRV O (x j))
    (disj : Pairwise (fun i j => Disjoint (B i) (B j))) (cover : (⋃ i, B i) = D) :
    positiveSetWeight O v hv hO P S Rmap Vmap (C := C) s D hd pd complete =
      ∑ i, positiveSetWeight O v hv hO P S Rmap Vmap (C := C) s (B i) (hb i) (pb i) complete := by
  have part i := positiveSetWeight_spec O v hv hO P S Rmap Vmap (C := C) s complete (B i) (hb i) (pb i)
  apply single_chart_weight O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat
    (positiveSetWeight_spec O v hv hO P S Rmap Vmap (C := C) s complete D hd pd)
  have eq : codeTuple O ⁻¹' D = ⋃ i, codeTuple O ⁻¹' B i := by rw [← cover,Set.preimage_iUnion]
  rw [eq]
  exact finiteChartWeight_partition _ _ _ _ _ (fun i j ne => (disj ne).preimage _) part

end GeneralizedEuler.Section4
