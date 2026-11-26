module

public import Section4.BoxRanksFromLifts
public import Section4.ResidueProductProfiles
public import Section4.ResidueBaseValues
import all Section4.RVScissorRealization
import all Section4.TaggedLiftRealization
import all Section4.RVFamilyOperations
import all Section4.RVFamilySemiring
import all Section4.Objects
import all Section4.BoxScaleProfiles
import all Section4.Factors

/-! A nonempty residue object may be multiplied into both tagged lifts
before recovering the maximal box vectors in Corollary 4.22a. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject Set
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (G : Submodule F (Additive O.ValueGroupˣ))
  {J JS : Language} [J.Structure K] [J.Structure (Residue O)]
  [JS.Structure (SignedValueGroup O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
variable (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (A : Set (SignedValueGroup O))
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (liftIso : ∀ {k} (D E : Set (Fin k → SignedValueGroup O)), A.Definable JS D → A.Definable JS E →
    ∀ f : D ≃ E, A.Definable JS {z : Fin k ⊕ Fin k → SignedValueGroup O | ∃ x : D, x.val = z ∘ Sum.inl ∧ (f x).val = z ∘ Sum.inr} →
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
        (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D) (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) E))
local notation "M" => canonicalStructure (L := J) O hO P
local notation "val" => signedLabel O hO
local notation "sh" => taggedSharp (S := S) val A defSharp

variable [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F (Additive O.ValueGroupˣ)]
local notation "V" => Additive O.ValueGroupˣ

include hv hs agrees units clamp powers in
theorem maximal_box_vectors_of_residue_product_equality
    (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
    (qe : ∀ {I : Type} [Finite I] (φ : SortedFormula J F (FullRVVariables S I)),
      ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧ ∀ x, q.realize M x ↔ φ.realize M x)
    {k : ℕ} (U W : Over (J := JS) A k)
    {l : ℕ} (R : RVObject M S l) (res : R.IsResidue M S val) (nonempty : R.carrier.Nonempty)
    (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet M S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
    (eq : objectClass M S ⟨l,R⟩ * valueFactorHom M S val A defSharp liftIso (taggedValueClass A U) =
      objectClass M S ⟨l,R⟩ * valueFactorHom M S val A defSharp liftIso (taggedValueClass A W))
    {T : Type*} [Fintype T] (t : T → V) (old : ∀ j, t j ∈ G) (nonneg : ∀ j, 0 ≤ t j)
    {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)]
    (leDef : (G : Set V).Definable JG {x : Fin 2 → V | x 0 ≤ x 1})
    (step : V) (pos : 0 < step)
    (sat : ∀ fs : Finset V, UnaryValueSaturation JG (↑(G ⊔ Submodule.span F (fs : Set V)) : Set V))
    (D : Fin U.tags → Fin k → BoxSide V) (E : Fin W.tags → Fin k → BoxSide V)
    (du : ∀ a i, (G : Set V).Definable JG {x : Unit → V | x () ∈ (D a i).domain})
    (dw : ∀ a i, (G : Set V).Definable JG {x : Unit → V | x () ∈ (E a i).domain})
    (wu : ∀ a i l, D a i = .bounded l → 0 < l) (ww : ∀ a i l, E a i = .bounded l → 0 < l)
    (pu : ∀ a, unsignedPoint O A U '' {p : U.points A | valuePointTag U p = a} = {z | ∀ i, z i ∈ (D a i).domain})
    (pw : ∀ a, unsignedPoint O A W '' {p : W.points A | valuePointTag W p = a} = {z | ∀ i, z i ∈ (E a i).domain}) :
    {p | Maximal (· ∈ Set.range (fun a => boxScaleCounts (F := F) (D a) t)) p} =
    {p | Maximal (· ∈ Set.range (fun b => boxScaleCounts (F := F) (E b) t)) p} := by
  let H (j : T) := G ⊔ scaleSpace F (t j)
  let fam := RVFamily.single R.carrier R.definable
  have iso : (fam.product (sh U)).Iso (fam.product (sh W)) := by
    apply (RVFamily.cls_eq_iff _ _).mp
    have same := congrArg (RVFamily.realizeScissors M S) eq
    simpa only [map_mul,RVFamily.realizeScissors_class,realize_tagged_lift,RVFamily.cls_product] using same
  obtain ⟨r,hr⟩ := nonempty
  let pt : fam.Points := ⟨(),r,hr⟩
  have oldValues (a : fam.Points) (i : fam.Coord a.1) :
      Additive.ofMul (RVValueSection.valueCoordinate (a.2.val i)) ∈ G := by
    obtain ⟨y,_,yb,same⟩ := residue_unsigned_representatives O hO P S witness R.carrier R.definable res a.2
    have sameCoord := valueCoordinate_eq_of_unsigned O (congrFun same i)
    rw [← sameCoord]
    exact base ⟨y i,yb i⟩
  have profiles := quotient_profiles_of_residue_product_iso O v hv s hs G hO P g agrees units clamp powers
    S A defSharp base qe fam pt oldValues U W iso H (fun _ => le_sup_left)
  let ranks (p : (i : T) → Submodule F (V ⧸ H i)) := fun i => Module.finrank F (p i)
  have same := congrArg (fun data => ranks '' data) profiles
  simp only [← Set.range_comp] at same
  apply maximal_box_vectors G t old nonneg leDef step pos sat D E du dw wu ww
  rw [← box_union_profiles G t (valuePointTag U) (unsignedPoint O A U) D pu,
    ← box_union_profiles G t (valuePointTag W) (unsignedPoint O A W) E pw]
  exact same

end GeneralizedEuler.Section4
