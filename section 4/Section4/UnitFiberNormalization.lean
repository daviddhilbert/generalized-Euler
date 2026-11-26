module

public import Section4.PureFactorAssignments
public import Section4.FiniteBaseFibers
import all Section4.SignedTensorFactors
import all Section4.SignedRectangleFactors
import all Section4.ResidueWeights
import all Section4.ValuePullback
import all Section4.Objects
import all Section4.FiniteScissors
import all Section2.RVMonomials
import all Section2.RVDefinableEquivalence

/-! Divide a positive fixed-value fiber by a tuple from the base. The
result is a definable subset of the positive units in the original degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {n : ℕ}

theorem signed_value_fiber_definable (y : Fin n → RV0 O) (hy : ∀ i, y i ∈ S.carrier .rv) :
    isRVSet _ S {x : Fin n → RV0 O | signedValue O hO ∘ x = signedValue O hO ∘ y} := by
  let Var := fun u => (S.carrier u : Type _) ⊕ RVVariables (Fin n) u
  let M := canonicalStructure (L := J) O hO P
  have each (i : Fin n) : isRVSet M S {x : Fin n → RV0 O | signedValue O hO (x i) = signedValue O hO (y i)} := by
    let a : SortedTerm J F Var .rv := .var (.inr i)
    let b : SortedTerm J F Var .rv := .var (.inl ⟨y i,hy i⟩)
    exact ⟨rvSameSignedValueFormula a b,fun w => (realize_rvSameSignedValueFormula O hO P a b (fun u => Sum.elim Subtype.val (w u))).symm⟩
  unfold isRVSet
  convert SortedDefinableOver.iInter each using 1
  ext w; rw [Set.mem_iInter]; exact funext_iff

theorem divide_fiber_equivalent (D : Set (Fin n → RV0 O)) (hd : isRVSet _ S D) (y : Fin n → RV0 O)
    (hy : ∀ i, y i ∈ S.carrier .rv) (ny : ∀ i, y i ≠ 0) :
    RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier D ((fun x => x / y) '' D) := by
  let div (x : Fin n → RV0 O) := x / y
  have inj : Function.Injective div := fun x z eq => funext fun i => (div_left_inj' (ny i)).mp (congrFun eq i)
  let e := Equiv.Set.imageOfInjOn div D inj.injOn
  refine ⟨e,?_⟩
  let H := RVVariables (Fin n ⊕ Fin n)
  let M := canonicalStructure (L := J) O hO P
  have dg : isRVSet M S {w : Fin n ⊕ Fin n → RV0 O | w ∘ Sum.inl ∈ D} := isRVSet_precomp Sum.inl hd
  have rows i := definable_rv_division_coordinate (L := J) (Var := H) O hO P (A := S.carrier) ⟨y i,hy i⟩ (.inl i) (.inr i)
  convert dg.inter (SortedDefinableOver.iInter rows) using 1
  ext w
  change (∃ t : D, t.val = _ ∧ div t.val = _) ↔ _ ∧ _
  simp only [Set.mem_iInter]
  exact ⟨fun ⟨t,ht,eq⟩ => ⟨(congrArg (· ∈ D) ht).mp t.property,fun i => (congrFun eq i).symm.trans (congrArg (· / y i) (congrFun ht i))⟩,
    fun h => ⟨⟨_,h.1⟩,rfl,funext fun i => (h.2 i).symm⟩⟩

variable [Field F] [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))

include hv in
theorem normalize_unit_fiber (D : Set (Fin n → RV0 O)) (hd : isRVSet _ S D) (y : Fin n → RV0 O)
    (hy : ∀ i, y i ∈ S.carrier .rv) (ny : ∀ i, y i ≠ 0)
    (fiber : ∀ x ∈ D, signedValue O hO ∘ x = signedValue O hO ∘ y) :
    ∃ B : Set (Fin n → v.ker), ∃ _hb : isRVSet _ S (unitSet O v (Equiv.refl _) B),
      RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier D (unitSet O v (Equiv.refl _) B) := by
  let E := (fun x => x / y) '' D
  let B := (unitTuple O v (Equiv.refl _)) ⁻¹' E
  have iso := divide_fiber_equivalent O hO P S D hd y hy ny
  have sub : E ⊆ unitSet O v (Equiv.refl (Fin n)) Set.univ := by
    rw [← unit_sharp_one (J := J) O v hv hO P]
    rintro _ ⟨x,hx,rfl⟩
    have equal i : signedValue O hO (x i) = signedValue O hO (y i) := congrFun (fiber x hx) i
    have one i : signedValue O hO ((x/y) i) = 1 := by
      change signedValue O hO (x i / y i) = 1
      exact (map_div₀ (signedValue O hO) (x i) (y i)).trans (by
        rw [equal i,div_self ((map_ne_zero _).mpr (ny i))])
    refine ⟨fun i h => ?_,?_⟩
    · change (x/y) i = 0 at h
      exact zero_ne_one (((map_zero (signedValue O hO)).symm.trans (congrArg (signedValue O hO) h.symm)).trans (one i))
    · exact funext fun i => by change (signedValue O hO ((x/y) i)).unzeroD 1 = 1; rw [one]; rfl
  have eq : unitSet O v (Equiv.refl _) B = E := by
    ext x
    exact ⟨fun ⟨b,hb,he⟩ => he ▸ hb,fun hx => by obtain ⟨b,_,rfl⟩ := sub hx; exact ⟨b,hx,rfl⟩⟩
  rw [← show unitSet O v (Equiv.refl _) B = (fun x => x / y) '' D from eq] at iso
  exact ⟨B,rv_equivalent_target_definable iso,iso⟩

end GeneralizedEuler.Section4
