module

public import Section4.TensorDescent
public import Section4.EmptyProductCoordinates
import all Section4.NormalRectangles
import all Section4.ResidueProducts
import all Section4.ResidueWeights
import all Section4.ValuePadding
import all Section4.RectangleClasses
import all Section4.ValueScissors
import all Section4.LocalRVMeasure

/-! The tensor valuation on the positive value pullback and on an
arbitrary homogeneous positive residue set. -/
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
local instance pureUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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
variable (complete : ∀ {n} (U : Set (Fin n → RV0 O)), isRVSet _ S U → (∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) →
  AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' U))

variable (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))
variable (covers : ∀ {n} (U : Set (Fin n → RV0 O)), GoodRVSet _ S (IsPositiveRV O) U →
  HasRectangleCover (JG := JG) (G := G) O v hO P S n U)

local notation "μ[" n "]" => tensorLocalMeasure (k := n) O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete

include pull in
theorem positive_sharp_assignment {r} (D : Set (Fin r → Additive O.ValueGroupˣ)) (hd : (G : Set _).Definable JG D) :
    μ[r].assigned (positiveSharp O v D) ((1 : R) ⊗ₜ[C] Vmap (pieceClass D hd)) := by
  let hu := unit_univ_definable O v hv hO P S (Equiv.refl (Fin 0))
  let z : NormalRectangle (JG := JG) (G := G) O v hO P S r := ⟨0,r,Nat.zero_add _,Set.univ,D,hu,hd⟩
  have unit : unitWeight O v hv hO P S (Equiv.refl (Fin 0)) Set.univ hu = 1 :=
    (entireUnitWeight_power O v hv hO P S 0).trans (pow_zero _)
  have wt : z.tensor hv Rmap Vmap (C := C) = 1 ⊗ₜ[C] Vmap (pieceClass D hd) := by
    change Rmap (unitWeight O v hv hO P S _ _ hu) ⊗ₜ[C] _ = _
    rw [unit,map_one]
  have model := z.assigned hv powers lang e Rmap Vmap resBalance valBalance s hs sat complete @pull
  rw [wt] at model
  have left : unitSet O v (Equiv.refl (Fin 0)) Set.univ = Set.univ :=
    Set.eq_univ_iff_forall.mpr (fun _ => ⟨fun i => i.elim0,Set.mem_univ _,Subsingleton.elim _ _⟩)
  apply μ[r].transfer _ model
  change RVDefinablyEquivalent _ S.carrier _ (productSet (unitSet O v (Equiv.refl (Fin 0)) _) (positiveSharp O v D))
  rw [left]; exact rv_empty_product_left (pull hd)

include pull in
theorem positive_unit_assignment {m} (B : Set (Fin m → v.ker)) (hb : isRVSet _ S (unitSet O v (Equiv.refl _) B)) :
    μ[m].assigned (unitSet O v (Equiv.refl _) B) (Rmap (unitWeight O v hv hO P S (Equiv.refl _) B hb) ⊗ₜ[C] (1 : W)) := by
  let D : Set (Fin 0 → Additive O.ValueGroupˣ) := {0}
  have hd : (G : Set _).Definable JG D := zeroTuple_definable G 0
  let z : NormalRectangle (JG := JG) (G := G) O v hO P S m := ⟨m,0,rfl,B,D,hb,hd⟩
  have val : pieceClass D hd = 1 := pieceClass_degree_zero _ _
  have wt : z.tensor hv Rmap Vmap (C := C) = Rmap (unitWeight O v hv hO P S _ _ hb) ⊗ₜ[C] (1 : W) := by
    change _ ⊗ₜ[C] Vmap (pieceClass D hd) = _
    rw [val,map_one]
  have model := z.assigned hv powers lang e Rmap Vmap resBalance valBalance s hs sat complete @pull
  rw [wt] at model
  have right : positiveSharp O v D = Set.univ := Set.eq_univ_iff_forall.mpr
    (fun _ => ⟨fun i => i.elim0,Subsingleton.elim _ _,Subsingleton.elim _ _⟩)
  apply μ[m].transfer _ model
  change RVDefinablyEquivalent _ S.carrier _ (productSet _ (positiveSharp O v D))
  rw [right]; exact rv_empty_product_right hb

end GeneralizedEuler.Section4
