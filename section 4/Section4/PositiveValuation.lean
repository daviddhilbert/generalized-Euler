module

public import Section4.GraphProjectionSums
import all Section4.GraphProjectionSums
import all Section4.CanonicalChartCover
import all Section4.PackedGraph
import all Section4.CanonicalChartMaps
import all Section4.SliceWeights

/-! The weight of an arbitrary positive definable set is unique and
invariant under fixed-base definable bijections. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
def finiteChartWeight {A X T : Type*} [AddCommMonoid T] (carrier : A → Set X) (meas : A → Prop)
    (weight : ∀ a, meas a → T) (D : Set X) (t : T) : Prop :=
  ∃ (n : ℕ) (p : Fin n → A) (hp : ∀ i, meas (p i)),
    Pairwise (fun i j => Disjoint (carrier (p i)) (carrier (p j))) ∧ (⋃ i, carrier (p i)) = D ∧
      (∑ i, weight (p i) (hp i)) = t

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] {G : Submodule F (Additive O.ValueGroupˣ)}
local instance unsignedStructure : JG.Structure O.ValueGroupˣ :=
  inferInstanceAs (JG.Structure (Additive O.ValueGroupˣ))
variable  (lang : ValueLanguage (J := JG) G)
  {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W]
variable [Algebra C R] [Algebra C W] (e : C) (Rmap : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R) (Vmap : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)
  (resBalance : algebraMap C R e = Rmap (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = Vmap (eValue (J := JG) G))

variable {n : ℕ}


variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)


variable {k : ℕ}

def HasChartWeight (D : Set (Fin k → Additive (PositiveRV O))) (t : TensorProduct C R W) : Prop :=
  finiteChartWeight (ChartPiece.carrier (T := Additive (PositiveRV O)) (V := Additive O.ValueGroupˣ) (F := F) (v := v) (G := G) (J := JG) (n := k) s)
    (@ChartPiece.measurable F K _ _ _ _ O _ _ v J _ _ hO P S JG _ G k)
    (@ChartPiece.tensorWeight F K _ _ _ _ O _ _ v hv J _ _ hO P S JG _ G C R W _ _ _ _ _ Rmap Vmap k) D t

variable (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))
include hs lang powers resBalance valBalance sat in
theorem single_chart_weight {D : Set (Fin k → Additive (PositiveRV O))} {x y}
    (hx : HasChartWeight O v hv hO P S Rmap Vmap s D (C := C) x)
    (hy : HasChartWeight O v hv hO P S Rmap Vmap s D (C := C) y) : x = y := by
  obtain ⟨_,p,hp,dp,cp,rfl⟩ := hx
  obtain ⟨_,q,hq,dq,cq,rfl⟩ := hy
  exact equal_chart_sums O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat p q hp hq dp dq (cp.trans cq.symm)

theorem chart_weight_exists {D : Set (Fin k → Additive (PositiveRV O))}
    (h : AdmitsCharts O v s G hO P S (JG := JG) D) :
    ∃ x : TensorProduct C R W, HasChartWeight O v hv hO P S Rmap Vmap s D x := by
  obtain ⟨l,p,hp,_,disj,cover⟩ := h
  exact ⟨_,l,p,hp,disj,cover,rfl⟩

variable (complete : ∀ {n} (U : Set (Fin n → RV0 O)), isRVSet _ S U → (∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) →
  AdmitsCharts O v s G hO P S (JG := JG) (codeTuple O ⁻¹' U))

include hs lang powers resBalance valBalance sat complete in
theorem positive_bijection_weights
    {D E : Set (Fin k → RV0 O)} (pd : ∀ x ∈ D, ∀ i, IsPositiveRV O (x i)) (pe : ∀ y ∈ E, ∀ i, IsPositiveRV O (y i))
    (iso : RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier D E) {x y : TensorProduct C R W}
    (hx : HasChartWeight O v hv hO P S Rmap Vmap s (codeTuple O ⁻¹' D) x)
    (hy : HasChartWeight O v hv hO P S Rmap Vmap s (codeTuple O ⁻¹' E) y) : x = y := by
  obtain ⟨f,hf⟩ := iso
  obtain ⟨l,a,ha,ne,disjoint,cv⟩ := complete (packGraph f) (packed_graph_definable f hf)
    (packed_graph_all f _ pd pe)
  let code (t : Additive (PositiveRV O)) := positiveRVToRV0 O t.toMul
  have inj : Function.Injective code := positiveRVToRV0_injective O
  obtain ⟨il,ir⟩ := lifted_graph_injections code f inj
  have lift {A : Set (Fin k → RV0 O)} (pos : ∀ z ∈ A, ∀ i, IsPositiveRV O (z i)) (z : A) :
      ∃ w : Fin k → Additive (PositiveRV O), code ∘ w = z.val := by
    choose w hw using fun i => exists_positiveRV_of_positive O (pos _ z.property i)
    exact ⟨fun i => Additive.ofMul (w i),funext hw⟩
  obtain ⟨left,right⟩ := lifted_graph_images code f (lift pd) (lift pe)
  obtain ⟨_,b,hb,db,cb,rfl⟩ := hx
  obtain ⟨_,c,hc,dc,cc,rfl⟩ := hy
  exact graph_projection_sums O v hv hO P powers S lang e Rmap Vmap resBalance valBalance s hs sat
    a ha ne disjoint (liftedGraph code f) cv (graphLeft k) (graphRight k) il ir
    b c hb hc db dc (cb.trans left.symm) (cc.trans right.symm)

end GeneralizedEuler.Section4
