module

public import Section4.MatchedResidueGraphs
public import Section4.MatchedFactorClasses
import all Section4.MatchedResidueGraphs
import all Section4.ResidueWeights
import all Section4.ResidueScissors
import all Section4.Factors
import all Section4.Objects

/-! A residue-factor graph, after specialization at an old pair of
values, identifies the two projected homogeneous classes inside RES. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} {J : Language} [J.Structure K] [J.Structure (Residue O)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O} {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {m n : ℕ}

def codedResidueSet (D : Set (Fin m → Residue O)) : Set (Fin m → RV0 O) :=
  (fun x => residueRV O ∘ x) '' D

def residueSetEquiv (D : Set (Fin m → Residue O)) : D ≃ codedResidueSet D :=
  Equiv.Set.imageOfInjOn _ _ (fun _ _ _ _ h => funext fun j => residueRV_injective O (congrFun h j))

omit [Field F] in
theorem residueGraph_equivalent (R : Set ((Fin m → Residue O) × (Fin n → Residue O)))
    (hr : isRVSet _ S (residueGraphCode R))
    (p : {a // ∃ b, (a,b) ∈ R} ≃ {b // ∃ a, (a,b) ∈ R})
    (relation : ∀ a b, (a.val,b.val) ∈ R ↔ p a = b) :
    RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
      (codedResidueSet {a | ∃ b, (a,b) ∈ R}) (codedResidueSet {b | ∃ a, (a,b) ∈ R}) := by
  let left := residueSetEquiv (O := O) {a | ∃ b, (a,b) ∈ R}
  let right := residueSetEquiv (O := O) {b | ∃ a, (a,b) ∈ R}
  let q := left.symm.trans (p.trans right)
  refine ⟨q,?_⟩
  unfold isRVSet at hr
  convert hr using 1
  ext z
  change (∃ x, x.val = z .rv ∘ Sum.inl ∧ (q x).val = z .rv ∘ Sum.inr) ↔ _
  constructor
  · rintro ⟨x,hx,hy⟩
    obtain ⟨a,rfl⟩ := left.surjective x
    have eq : q (left a) = right (p a) := congrArg (fun t => right (p t)) (left.symm_apply_apply a)
    exact ⟨a.val,(p a).val,(relation _ _).mpr rfl,hx,(congrArg Subtype.val eq).symm.trans hy⟩
  · rintro ⟨u,w,h,hu,hw⟩
    let a : {a // ∃ b, (a,b) ∈ R} := ⟨u,w,h⟩
    let b : {b // ∃ a, (a,b) ∈ R} := ⟨w,u,h⟩
    have eq : q (left a) = right b := (congrArg (fun t => right (p t)) (left.symm_apply_apply a)).trans (congrArg right ((relation a b).mp h))
    exact ⟨left a,hu,(congrArg Subtype.val eq).trans hw⟩

variable [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))

variable (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

include hv hs in
theorem unitSet_match_projection (U : Set (Fin m → v.ker)) (D : Set (Fin m → Residue O))
    (realized : ∀ x ∈ D, ∃ u ∈ U, kernelResidue v ∘ u = x) :
    unitSet O v (Equiv.refl _) (U ∩ (fun u => kernelResidue v ∘ u) ⁻¹' D) = codedResidueSet D := by
  ext x
  constructor
  · rintro ⟨u,⟨_,h⟩,rfl⟩
    exact ⟨_,h,funext fun j => residueRV_kernel hv s hs (u j)⟩
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨u,hu,rfl⟩ := realized _ hz
    exact ⟨u,⟨hu,hz⟩,(funext fun j => residueRV_kernel hv s hs (u j)).symm⟩

theorem matched_residue_classes (R : Set ((Fin m → Residue O) × (Fin m → Residue O)))
    (hr : isRVSet _ S (residueGraphCode R))
    (p : {a // ∃ b, (a,b) ∈ R} ≃ {b // ∃ a, (a,b) ∈ R})
    (relation : ∀ a b, (a.val,b.val) ∈ R ↔ p a = b)
    {A B : Set (Fin m → v.ker)}
    (left : unitSet O v (Equiv.refl _) A = codedResidueSet {a | ∃ b, (a,b) ∈ R})
    (right : unitSet O v (Equiv.refl _) B = codedResidueSet {b | ∃ a, (a,b) ∈ R}) :
    ∃ (ha : isRVSet _ S (unitSet O v (Equiv.refl _) A)) (hb : isRVSet _ S (unitSet O v (Equiv.refl _) B)),
      unitWeight O v hv hO P S (Equiv.refl _) A ha = unitWeight O v hv hO P S (Equiv.refl _) B hb := by
  have iso := residueGraph_equivalent R hr p relation
  rw [← left,← right] at iso
  have ha := rv_equivalent_target_definable iso.symm
  have hb := rv_equivalent_target_definable iso
  exact ⟨ha,hb,residue_class_iso _ _ _ _ iso⟩

end GeneralizedEuler.Section4.NormalRectangle
