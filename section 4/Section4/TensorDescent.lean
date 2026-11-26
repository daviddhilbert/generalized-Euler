module

public import Section4.RectangleMultiplicativity
public import Section4.MultiplicativeDescent
import all Section4.ResidueProducts
import all Section4.NormalRectangles
import all Section4.ValuePadding
import all Section4.ValueScissors
import all Section4.LocalRVMeasure

/-! The graph construction gives a semiring homomorphism on the actual
graded RV scissors presentation. -/
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
local instance descendUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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
theorem tensor_assignment_one (U : RVObject _ S 0) (h : ∃ x, U.carrier = {x}) :
    μ[0].assigned U.carrier 1 := by
  let D : Set (Fin 0 → Additive O.ValueGroupˣ) := {0}
  have hD : (G : Set _).Definable JG D := zeroTuple_definable G 0
  let b := unit_univ_definable O v hv hO P S (Equiv.refl (Fin 0))
  let z : NormalRectangle (JG := JG) (G := G) O v hO P S 0 := ⟨0,0,rfl,Set.univ,D,b,hD⟩
  have unit : unitWeight O v hv hO P S (Equiv.refl (Fin 0)) Set.univ b = 1 :=
    (entireUnitWeight_power O v hv hO P S 0).trans (pow_zero _)
  have val : pieceClass D hD = 1 := pieceClass_degree_zero _ _
  have wt : z.tensor hv Rmap Vmap (C := C) = 1 := by
    change Rmap (unitWeight O v hv hO P S _ _ b) ⊗ₜ[C] Vmap (pieceClass D hD) = _
    rw [unit,val,map_one,map_one]; rfl
  have model := z.assigned hv powers lang e Rmap Vmap resBalance valBalance s hs sat complete @pull
  rw [wt] at model
  obtain ⟨x,hx⟩ := h
  let a : U.carrier := ⟨x,hx.symm ▸ Set.mem_singleton x⟩
  let y : z.points := ⟨Sum.elim (fun i => i.elim0) (fun i => i.elim0),
    ⟨fun i => i.elim0,Set.mem_univ _,Subsingleton.elim _ _⟩,
    fun i => i.elim0,Subsingleton.elim _ _,Subsingleton.elim _ _⟩
  have only (t : U.carrier) : t = a := Subtype.ext (show t.val ∈ ({x} : Set _) from hx ▸ t.property)
  exact μ[0].transfer (singleton_equivalent U.definable (z.points_definable @pull) a y only
    (fun t => Subtype.ext (funext fun i => by rcases i with i | i <;> exact i.elim0))) model

variable (minus : rv O (-1) ∈ S.carrier .rv)
  (rvSat : ∀ {n} (D : ℕ → Set (Fin n → RV0 O)), (∀ i, isRVSet _ S (D i)) → Antitone D →
    (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)

def rvTensorAssignment : RVSemiring (canonicalStructure (L := J) O hO P) S →+* TensorProduct C R W :=
  LocalRVMeasure.descend (fun n => μ[n])
    (fun U => object_measure_exists O hO P S μ[_] U minus rvSat)
    (tensor_assignment_one O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete @pull)
    (fun {_ _} _ _ {_ _} hx hy => tensor_assignment_product O v hv hO P powers S lang e Rmap Vmap resBalance valBalance
      s hs sat complete @pull @covers hx hy)

theorem rvTensorAssignment_assigned {n} (U : RVObject _ S n) {x : TensorProduct C R W} (hx : μ[n].assigned U.carrier x) :
    rvTensorAssignment O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat complete @pull @covers
      minus @rvSat (objectClass _ S ⟨n,U⟩) = x := by
  unfold rvTensorAssignment
  apply LocalRVMeasure.descend_assigned
  exact hx

end GeneralizedEuler.Section4
