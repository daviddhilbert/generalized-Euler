module

public import Section4.MixedMatchFactors
public import Section4.NormalRectangles
import all Section4.MixedMatchFactors
import all Section4.RectangleClasses
import all Section4.CanonicalChartMaps
import all Section4.SignedShears
import all Section4.NormalRectangles

/-! Select a base value pair in a nonempty definable value graph.
A fixed-base point in its positive RV pullback supplies both tuples. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O} (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (G : Submodule F (Additive O.ValueGroupˣ))
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D → isRVSet _ S (positiveSharp O v D))
  (old : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)

include hv hs pull old witness in
theorem old_value_pair {m n : ℕ}
    {D : Set ((Fin m → Additive O.ValueGroupˣ) × (Fin n → Additive O.ValueGroupˣ))}
    (hd : (G : Set _).Definable JG (pairedSet D)) (ne : D.Nonempty) :
    ∃ a b, (a,b) ∈ D ∧ (∀ i, a i ∈ G) ∧ (∀ j, b j ∈ G) := by
  let e : Fin m ⊕ Fin n ≃ Fin (m+n) := finSumFinEquiv
  let W := {t : Fin (m+n) → Additive O.ValueGroupˣ | t ∘ e ∈ pairedSet D}
  have dw : (G : Set _).Definable JG W := hd.preimage_comp e
  have nw : W.Nonempty := by
    obtain ⟨⟨a,b⟩,h⟩ := ne
    refine ⟨Sum.elim a b ∘ e.symm,?_⟩
    change ((Sum.elim a b ∘ e.symm) ∘ e) ∈ pairedSet D
    simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using (show Sum.elim a b ∈ pairedSet D from h)
  obtain ⟨_,⟨z,hz,rfl⟩,base⟩ := witness _ (pull dw) (positiveSharp_nonempty O v s hs W nw)
  have allOld (i) : v (z i) ∈ G := by
    have h := old ⟨codeTuple O z i,base i⟩
    change Additive.ofMul (RVValueSection.valueCoordinate (positiveRVToRV0 O (z i).toMul)) ∈ G at h
    rw [hv]
    have hval : RVValueSection.valueCoordinate (positiveRVToRV0 O (z i).toMul) = positiveValueMap O (z i).toMul :=
      Units.ext ((RVValueSection.coe_valueCoordinate ((positiveRVToRV0_pos O _).ne_zero O)).trans (positiveValueMap_coe O _).symm)
    rwa [hval] at h
  exact ⟨_,_,hz,fun i => allOld (e (.inl i)),fun j => allOld (e (.inr j))⟩

end GeneralizedEuler.Section4
