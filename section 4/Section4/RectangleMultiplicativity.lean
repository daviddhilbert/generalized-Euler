module

public import Section4.NormalRectangleCover
public import Section4.ProductAssignment
import all Section4.NormalRectangles
import all Section4.LocalRVMeasure
import all Section4.NormalRectangleCover

/-! Multiplicativity of the chart valuation in arbitrary degree, obtained by
cutting positive carriers into the fixed-base rectangles of the graph proof. -/
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
local instance productWeightUnsignedStructure : JG.Structure O.ValueGroupˣ :=
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

include pull covers in
theorem tensor_assignment_product {k l} {I H : Type} {U : Set (I → RV0 O)} {V : Set (H → RV0 O)} {x y : TensorProduct C R W}
    (hx : μ[k].assigned U x) (hy : μ[l].assigned V y) :
    μ[k+l].assigned (productSet U V) (x*y) := by
  apply LocalRVMeasure.product_of_models μ[k] μ[l] μ[k+l] _ hx hy
  intro A B ha hb
  obtain ⟨_,a,c,da,ca,ac⟩ := covers A ha
  obtain ⟨_,b,d,db,cb,bd⟩ := covers B hb
  let w {n} (t : NormalRectangle (JG := JG) (G := G) O v hO P S n) := t.tensor hv Rmap Vmap (C := C)
  have model {n} (t : NormalRectangle (JG := JG) (G := G) O v hO P S n) :
      μ[n].assigned t.points (w t) :=
    t.assigned hv powers lang e Rmap Vmap resBalance valBalance s hs sat complete @pull
  have aw := μ[k].assigned_partition a (w ∘ c) da ca (fun i => μ[k].transfer (ac i) (model (c i)))
  have bw := μ[l].assigned_partition b (w ∘ d) db cb (fun i => μ[l].transfer (bd i) (model (d i)))
  rw [μ[k].unique (μ[k].assigned_model A ha) aw,
      μ[l].unique (μ[l].assigned_model B hb) bw]
  apply μ[k+l].product_of_partitions a b (w ∘ c) (w ∘ d) da db ca cb
  intro i j
  obtain ⟨z,iso,eq⟩ := (c i).product_rectangle hv Rmap Vmap @pull (d j) (C := C)
  exact μ[k+l].transfer ((rv_product_equivalent (ac i) (bd j)).trans iso) (eq ▸ model z)

end GeneralizedEuler.Section4
