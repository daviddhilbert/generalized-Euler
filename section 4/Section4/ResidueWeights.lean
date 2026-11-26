module

public import Section4.DefinableResidueMatrices
import all Section4.SignedRectangleFactors
import all Section4.DefinableResidueMatrices
import all Section4.PositivePresentations
import all Section4.Objects
import all Section4.ResidueScissors
import all Section4.FiniteScissors
import all Section2.RVMonomials
import all Section2.RVVectorSpace
import all Section2.SignedValue

/-! Positive unit tuples as actual homogeneous classes in RES. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {I : Type} {m : ℕ} (ei : Fin m ≃ I)
  (D : Set (I → v.ker))

def unitSet := unitTuple O v ei '' D

theorem unitSet_positive (x : Fin m → RV0 O) (hx : x ∈ unitSet O v ei D) (j : Fin m) :
    IsPositiveRV O (x j) := by obtain ⟨a,_,rfl⟩ := hx; exact positiveRVToRV0_pos O _

variable (hd : isRVSet _ S (unitSet O v ei D))
def unitObject := positiveObject O hO P S _ hd (unitSet_positive O v ei D)

include hv in
theorem unitObject_residue : (unitObject O v hO P S ei D hd).IsResidue _ S (signedLabel O hO) := by
  apply (Set.finite_singleton (1 : Fin m → SignedValueGroup O)).subset
  rintro _ ⟨x,rfl⟩
  obtain ⟨a,_,eq⟩ := x.property
  change signedLabel O hO ∘ x.val = 1
  rw [← eq]
  funext i
  have unit : v (a (ei i)).val = 0 := (a (ei i)).property
  change signedLabel O hO (positiveRVToRV0 O (a (ei i)).val.toMul) = 1
  rw [signedLabel_code,← hv,unit]; rfl

def unitWeight := residueClass (unitObject O v hO P S ei D hd) (unitObject_residue O v hv hO P S ei D hd)

include hv in
theorem unit_univ_definable : isRVSet _ S (unitSet O v ei Set.univ) := by
  let M := canonicalStructure (L := J) O hO P
  let Var := fun s => (S.carrier s : Type _) ⊕ RVVariables (Fin m) s
  let t (i : Fin m) : SortedTerm J F Var .rv := .var (.inr i)
  have guard (i : Fin m) : isRVSet M S {x : Fin m → RV0 O | signedValue O hO (x i) = 1} := by
    refine ⟨rvSameSignedValueFormula (t i) rvOneTerm,fun a => ?_⟩
    apply Iff.trans _ (realize_rvSameSignedValueFormula O hO P (t i) rvOneTerm (fun s => Sum.elim Subtype.val (a s))).symm
    change signedValue O hO (a .rv i) = 1 ↔ signedValue O hO (a .rv i) = signedValue O hO 1
    rw [map_one]
  unfold isRVSet
  convert SortedDefinableOver.iInter guard using 1
  ext a
  change (∃ x, x ∈ Set.univ ∧ unitTuple O v ei x = a .rv) ↔ a ∈ ⋂ i, {a | signedValue O hO (a .rv i) = 1}
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,Set.mem_univ,true_and]
  constructor
  · rintro ⟨x,eq⟩ i
    rw [← eq]
    let z := (x (ei i)).val
    have val : v z = 0 := (x (ei i)).property
    have h : signedLabel O hO (positiveRVToRV0 O z.toMul) = 1 := by rw [signedLabel_code,← hv,val]; rfl
    have nz : signedValue O hO (positiveRVToRV0 O z.toMul) ≠ 0 :=
      (map_ne_zero _).mpr ((positiveRVToRV0_pos O _).ne_zero O)
    change signedValue O hO (positiveRVToRV0 O z.toMul) = 1
    cases e : signedValue O hO (positiveRVToRV0 O z.toMul) using WithZero.recZeroCoe with
    | zero => exact (nz e).elim
    | coe t =>
      change (signedValue O hO _).unzeroD 1 = 1 at h
      rw [e] at h
      change t = 1 at h; rw [h]; rfl
  · intro all
    have each (i) : ∃ x : v.ker, positiveRVToRV0 O x.val.toMul = a .rv i := by
      have nz : a .rv i ≠ 0 := fun h => by simpa [h] using all i
      have label : signedLabel O hO (a .rv i) = 1 := by rw [signedLabel,all i]; rfl
      obtain ⟨x,hx⟩ := exists_positiveRV_of_positive O ((signedLabel_pos O hO nz).mp (congrArg Prod.fst label))
      have value := (signedLabel_code O hO x).symm.trans (hx ▸ label)
      have hval := congrArg (fun p : SignedValueGroup O => Additive.ofMul p.2) value
      exact ⟨⟨Additive.ofMul x,(hv _).trans hval⟩,hx⟩
    choose x hx using each
    exact ⟨x ∘ ei.symm,funext fun i => by simpa [unitTuple,codeTuple] using hx i⟩

theorem unitWeight_congr {C : Set (I → v.ker)} (eq : D = C) (hc : isRVSet _ S (unitSet O v ei C)) :
    unitWeight O v hv hO P S ei D hd = unitWeight O v hv hO P S ei C hc := by subst C; rfl

end GeneralizedEuler.Section4
