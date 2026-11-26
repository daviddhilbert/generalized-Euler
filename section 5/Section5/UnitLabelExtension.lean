module

public import Section5.BlowupClassProducts
public import Mathlib.Data.Fin.Tuple.Basic
import all Section2.RVMonomials
import all Section2.SortedSyntax
import all Section4.Objects

/-! A lower-degree presentation of a locus is equivalent to one
whose last structure coordinate is the constant unit. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}
  (U : RVObject M S k)

abbrev rvUnitValue := M.funMap .rvOne (fun i => i.elim0)

theorem appendUnitLabel_definable :
    SortedDefinableOver M S.carrier (rvGraph (fun x : U.carrier => Fin.snoc (U.label x) (rvUnitValue (M := M)))) := by
  let V := RVVariables (Fin U.arity ⊕ Fin (k+1))
  let rename : ∀ s, RVVariables (Fin U.arity ⊕ Fin k) s → V s
    | .vf => PEmpty.elim
    | .rv => Sum.map id Fin.castSucc
  have graph := U.graph.pullback_relabel rename
  have one := SortedDefinableOver.coordinate_eq_term (M := M) (A := S.carrier) (Var := V)
    .rv (.inr (Fin.last k)) rvOneTerm
  convert graph.inter one using 1
  ext x
  have realizes (a : ∀ s, WithBase S.carrier V s → X s) :
      (rvOneTerm : SortedTerm L E (WithBase S.carrier V) .rv).realize M a =
        rvUnitValue (M := M) := by
    unfold rvOneTerm SortedTerm.realize
    exact congrArg (M.funMap .rvOne) (funext fun i => i.elim0)
  simp only [Set.mem_inter_iff,realizes]
  change (∃ a : U.carrier, a.val = x .rv ∘ Sum.inl ∧
    Fin.snoc (U.label a) (rvUnitValue (M := M)) = x .rv ∘ Sum.inr) ↔
    (∃ a : U.carrier, a.val = x .rv ∘ Sum.inl ∧
      U.label a = x .rv ∘ Sum.inr ∘ Fin.castSucc) ∧ x .rv (.inr (Fin.last k)) = rvUnitValue (M := M)
  constructor
  · rintro ⟨a,ha,hl⟩
    refine ⟨⟨a,ha,?_⟩,?_⟩
    · funext i
      simpa only [Fin.snoc_castSucc,Function.comp_apply] using congrFun hl i.castSucc
    · simpa only [Fin.snoc_last,Function.comp_apply] using (congrFun hl (Fin.last k)).symm
  · rintro ⟨⟨a,ha,hl⟩,hone⟩
    refine ⟨a,ha,?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      exact hone.symm
    · rw [Fin.snoc_castSucc]
      exact congrFun hl j

@[expose] def appendUnitLabel
    (nonzero : rvUnitValue (M := M) ≠ M.funMap .rvZero (fun i => i.elim0)) : RVObject M S (k+1) where
  arity := U.arity
  carrier := U.carrier
  definable := U.definable
  label x := Fin.snoc (U.label x) (rvUnitValue (M := M))
  graph := appendUnitLabel_definable U
  nonzero x j := Fin.lastCases (by rw [Fin.snoc_last]; exact nonzero)
    (fun i => by rw [Fin.snoc_castSucc]; exact U.nonzero x i) j
  finiteFibers y := by
    apply (U.finiteFibers (y ∘ Fin.castSucc)).subset
    intro x hx
    change U.label x = y ∘ Fin.castSucc
    change Fin.snoc (U.label x) (rvUnitValue (M := M)) = y at hx
    funext i
    simpa only [Fin.snoc_castSucc,Function.comp_apply] using congrFun hx i.castSucc

theorem appendUnitLabel_finite_deletion
    (nonzero : rvUnitValue (M := M) ≠ M.funMap .rvZero (fun i => i.elim0)) (t : Fin k → X .rv) :
    {u ∈ Set.range (appendUnitLabel U nonzero).label | u ∘ (Fin.last k).succAbove = t}.Finite := by
  apply (Set.finite_singleton (Fin.snoc t (rvUnitValue (M := M)))).subset
  rintro _ ⟨⟨x,rfl⟩,h⟩
  let a : U.carrier := x
  have eq : U.label x = t := by
    funext i
    have hi := congrFun h i
    change (Fin.snoc (U.label a) (rvUnitValue (M := M)) : Fin (k+1) → X .rv)
      ((Fin.last k).succAbove i) = t i at hi
    rwa [Fin.succAbove_last,Fin.snoc_castSucc] at hi
  change (Fin.snoc (U.label a) (rvUnitValue (M := M)) : Fin (k+1) → X .rv) = _
  rw [eq]

/-- The original lower-degree object is recovered exactly on the zero
stratum of the elementary blowup in the added coordinate. -/
theorem appendUnitLabel_zero_class
    (nonzero : rvUnitValue (M := M) ≠ M.funMap .rvZero (fun i => i.elim0)) :
    objectClass M S ⟨k,zeroBlowupObject (appendUnitLabel U nonzero) (Fin.last k)
      (appendUnitLabel_finite_deletion U nonzero)⟩ = objectClass M S ⟨k,U⟩ := by
  apply scissors_sound M S
  apply RVRelation.iso
  change RVDefinablyEquivalent M S.carrier U.carrier U.carrier
  exact ⟨Equiv.refl _,definable_identity_label M S U.definable⟩

theorem canonical_rvUnit_nonzero
    {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
    (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O) :
    let N := canonicalStructure (L := L) O hO power
    rvUnitValue (M := N) ≠ N.funMap .rvZero (fun i => i.elim0) := by
  intro N
  change (1 : RV0 O) ≠ 0
  simpa only [map_one] using (rv_eq_zero_iff O).not.mpr (one_ne_zero : (1 : K) ≠ 0)

theorem appendUnitLabel_class
    {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
    (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
    (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
    (U : RVObject (canonicalStructure (L := L) O hO power) S k) :
    let N := canonicalStructure (L := L) O hO power
    objectClass N S ⟨k+1,appendUnitLabel U (canonical_rvUnit_nonzero O hO power)⟩ =
      objectClass N S ⟨k,U⟩ * objectClass N S ⟨1,residuePointObject O hO power S⟩ := by
  intro N
  let nz := canonical_rvUnit_nonzero (L := L) O hO power
  let W := appendUnitLabel U nz
  rw [blowup_original_class_factor O hO power S W (Fin.last k) (appendUnitLabel_finite_deletion U nz),
    appendUnitLabel_zero_class U nz]

end GeneralizedEuler.Section5
