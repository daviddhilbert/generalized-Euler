module

public import Section4.PositiveAdditivity
public import Section4.LocalRVMeasure
import all Section4.LocalRVMeasure
import all Section4.PositiveValuation
import all Section4.CanonicalChartCover

/-! The graph proof gives an additive, fixed-base isomorphism invariant
for all degree-k RV objects, with finite-to-one labels and arbitrary signs. -/
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
local instance objectWeightUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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



def tensorLocalMeasure : LocalRVMeasure (canonicalStructure (L := J) O hO P) S (IsPositiveRV O) k (TensorProduct C R W) where
  weight D h := positiveSetWeight O v hv hO P S Rmap Vmap s D h.1 h.2 complete
  cut D hd B hb disj cov := positiveSetWeight_partition O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete D hd.1 hd.2 B
    (fun i => (hb i).1) (fun i => (hb i).2) disj cov
  iso D E hd he h := positive_bijection_weights O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete hd.2 he.2 h
    (positiveSetWeight_spec O v hv hO P S Rmap Vmap s complete D hd.1 hd.2)
    (positiveSetWeight_spec O v hv hO P S Rmap Vmap s complete E he.1 he.2)

variable {T : Type*} [AddCommMonoid T] (μ : LocalRVMeasure (canonicalStructure (L := J) O hO P) S (IsPositiveRV O) k T)

omit [Field F] [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)] in
theorem object_measure_exists (U : RVObject _ S k) (minus : rv O (-1) ∈ S.carrier .rv)
    (rvSat : ∀ D : ℕ → Set (Fin k → RV0 O), (∀ i, isRVSet _ S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) : ∃ t, μ.assigned U.carrier t := by
  obtain ⟨l,A,B,ha,hb,pos,disj,cov,bij⟩ := positive_object_cover O hO P S U minus rvSat
  let c (i : Fin l) : LocalRVMeasure.Cell _ S (IsPositiveRV O) k (Fin U.arity) :=
    ⟨A i,ha i,B i,⟨hb i,pos i⟩,bij i⟩
  exact ⟨_,l,c,disj,cov,rfl⟩

end GeneralizedEuler.Section4
