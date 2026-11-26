module

public import Section4.StandardFrame
public import Section4.ReindexUnits
public import Section4.ArbitraryRectangleWeight
import all Section4.StandardFrame
import all Section4.PositiveValuation
import all Section4.SliceWeights
import all Section4.GraphProjectionSums
import all Section4.ResidueWeights
import all Section4.CanonicalChartMaps
import all Section4.RectangleClasses
import all Section4.ValueScissors

/-! The value of a standard rectangle over any definable value domain is
its prescribed pure tensor, with the residue and value degrees unchanged. -/
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
local instance standardUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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
theorem standard_rectangle_weight {m r : ℕ}
    (D : Set (Fin r → Additive O.ValueGroupˣ)) (hd : (G : Set _).Definable JG D)
    (B : Set (Fin m → v.ker))
    (hb : isRVSet _ S (unitSet O v (Equiv.refl _) B)) :
    HasChartWeight O v hv hO P S Rmap Vmap s
      (cartesian ((fun b : Fin m → v.ker => v.ker.subtype ∘ b) '' B) {z | v ∘ z ∈ D})
      (Rmap (unitWeight O v hv hO P S (Equiv.refl _) B hb) ⊗ₜ[C] Vmap (pieceClass D hd)) := by
  let A := standardFrame G m r
  let idx := standardIndex G m r
  obtain ⟨ha,eq⟩ := reindex_unit_class O v hv hO P powers S (Equiv.refl (Fin m)) (residueIndex A) idx.symm B hb
  have h := arbitrary_rectangle_weight O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat
    A D hd {b | b ∘ idx ∈ B} ha
  have carrier := standard_carrier (F := F) (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ)
    (m := m) (r := r) G v s D B
  have res : unitWeight O v hv hO P S (residueIndex A) {b | b ∘ idx ∈ B} ha = unitWeight O v hv hO P S (Equiv.refl _) B hb := eq
  rw [carrier,res] at h
  exact h

theorem code_cartesian {m r} (B : Set (Fin m → v.ker)) (D : Set (Fin r → Additive O.ValueGroupˣ)) :
    codeTuple O ⁻¹' cartesian (unitSet O v (Equiv.refl _) B) (positiveSharp O v D) =
      cartesian ((fun b : Fin m → v.ker => v.ker.subtype ∘ b) '' B) {z | v ∘ z ∈ D} := by
  ext x
  let l := stdLeft m r
  let g := stdRight m r
  change (codeTuple O (x ∘ l) ∈ unitSet O v (Equiv.refl _) B ∧ codeTuple O (x ∘ g) ∈ positiveSharp O v D) ↔
    (x ∘ l ∈ _ ∧ v ∘ (x ∘ g) ∈ D)
  apply and_congr
  · exact ⟨fun ⟨b,hb,eq⟩ => ⟨b,hb,codeTuple_injective O eq⟩,
      fun ⟨b,hb,eq⟩ => ⟨b,hb,congrArg (codeTuple O) eq⟩⟩
  · exact ⟨fun ⟨z,hz,eq⟩ => (codeTuple_injective O eq) ▸ hz,fun hz => ⟨_,hz,rfl⟩⟩

end GeneralizedEuler.Section4
