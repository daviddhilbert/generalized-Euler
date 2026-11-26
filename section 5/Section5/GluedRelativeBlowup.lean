module

public import Section5.RelativePositiveBlowup
public import Section5.RelativeGluedDeletion
public import Section5.ElementaryClassSteps
import all Section4.Scissors
import all Section4.Objects

/-! A local elementary blowup in one row glues to a genuine elementary
class step. The chosen head start remains available in both branches. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}

theorem rv_cast_carrier_equiv {a k : ℕ} (W : RVObject M S k) (ea : W.arity = a)
    (D : Set (Fin a → X .rv)) (he : ∀ x, x ∘ Fin.cast ea ∈ W.carrier ↔ x ∈ D) :
    RVDefinablyEquivalent M S.carrier W.carrier D := by
  have iso := rv_reindex_equivalent M S (finCongr ea.symm) W.carrier W.definable
  have eq : {x : Fin a → X .rv | x ∘ (finCongr ea.symm).symm ∈ W.carrier} = D :=
    Set.ext he
  rwa [eq] at iso

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {h m t k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "P" => RVVariables (Fin h)
local notation "U" => RVVariables (Fin m)
local notation "V" => RVVariables (Fin (k+1))
local notation "val" => CanonicalSort O

private theorem glued_positive_tags_equiv
    (neg : rv O (-1) ∈ S₀.carrier .rv)
    {B : Set (Fin h → RV0 O)} (defB : isRVSet 𝓜 S₀ B)
    {D : Set (SortedAssignment val (SumVariables P U))} (defD : SortedDefinableOver 𝓜 S₀.carrier D) :
    RVDefinablyEquivalent 𝓜 S₀.carrier
      (productSet (gluedRVTags B D) {s : Fin 1 → RV0 O | unsignedValue O (s 0) < 1 ∧ s 0 ≠ 0})
      (gluedRVTags B (relativePositiveTags O D)) := by
  let small := {s : Fin 1 → RV0 O | unsignedValue O (s 0) < 1 ∧ s 0 ≠ 0}
  let T := productSet (gluedRVTags B D) small
  have dT : isRVSet 𝓜 S₀ T := isRVSet_inter
    (isRVSet_precomp Sum.inl (gluedRVTags_definable defB defD))
    (isRVSet_precomp Sum.inr (nonzero_multipliers_definable O hO power S₀ neg))
  let e : Fin (h+(m+1)) ≃ Fin (h+m) ⊕ Fin 1 := (finSumFinEquiv (m := h+m) (n := 1)).symm
  have iso := rv_reindex_equivalent 𝓜 S₀ e T dT
  have eq : {x : Fin (h+(m+1)) → RV0 O | x ∘ e.symm ∈ T} = gluedRVTags B (relativePositiveTags O D) := by
    ext x
    let u : Fin (h+m) → RV0 O := x ∘ e.symm ∘ Sum.inl
    let v : Fin 1 → RV0 O := x ∘ e.symm ∘ Sum.inr
    let a : Fin h → RV0 O := x ∘ rvHead
    let b : Fin (m+1) → RV0 O := x ∘ rvTail
    have head : u ∘ rvHead = a := by
      funext i
      apply congrArg x
      simp only [e,Equiv.symm_symm,rvHead,Function.comp_apply,finSumFinEquiv_apply_left]
      exact Fin.ext rfl
    have tail : u ∘ rvTail = b ∘ Fin.castSucc := by
      funext i
      apply congrArg x
      simp only [e,Equiv.symm_symm,rvTail,Function.comp_apply,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
      exact Fin.ext rfl
    have last : v 0 = b (Fin.last m) := by
      apply congrArg x
      simp only [e,Equiv.symm_symm,rvTail,Function.comp_apply,finSumFinEquiv_apply_right]
      apply Fin.ext
      simp
    have strip : retainOldRVTags O (rvTupleAssignment b) = rvTupleAssignment (b ∘ Fin.castSucc) := by
      funext s i
      cases s
      · exact i.elim
      · rfl
    change ((u ∘ rvHead ∈ B ∧ appendAssignments (rvTupleAssignment (u ∘ rvHead))
      (rvTupleAssignment (u ∘ rvTail)) ∈ D) ∧ (unsignedValue O (v 0) < 1 ∧ v 0 ≠ 0)) ↔
      (a ∈ B ∧ appendAssignments (rvTupleAssignment a) (retainOldRVTags O (rvTupleAssignment b)) ∈ D ∧
        unsignedValue O (b (Fin.last m)) < 1 ∧ b (Fin.last m) ≠ 0)
    rw [head,tail,last,strip]
    exact and_assoc
  rwa [eq] at iso

theorem glued_relative_elementary_step
    (neg : rv O (-1) ∈ S₀.carrier .rv)
    (j : Fin (k+1)) (sel : Fin t → Fin h)
    {B : Set (Fin h → RV0 O)} (defB : isRVSet 𝓜 S₀ B)
    {D : Set (SortedAssignment val (SumVariables P U))}
    {G : Set (SortedAssignment val (SumVariables (SumVariables P U) V))}
    (defD : SortedDefinableOver 𝓜 S₀.carrier D) (defG : SortedDefinableOver 𝓜 S₀.carrier G)
    (headNonzero : ∀ p ∈ B, ∀ i, p (sel i) ≠ 0)
    (finiteBase : ∀ q : Fin t → RV0 O, {p ∈ B | p ∘ sel = q}.Finite)
    (valid : ∀ p ∈ B, ∃ a b, RelativeRVWitness D G 0 a (rvTupleAssignment p) ∧
      RelativeRVWitness D (relativeDeleteLabelGraph j G) 0 b (rvTupleAssignment p)) :
    ∃ (A : RVObject 𝓜 S₀ (t+k+1)) (Z : RVObject 𝓜 S₀ (t+k)) (N : RVObject 𝓜 S₀ (t+k+1)),
      RVDefinablyEquivalent 𝓜 S₀.carrier A.carrier (gluedRVTags B D) ∧
      RVDefinablyEquivalent 𝓜 S₀.carrier Z.carrier (gluedRVTags B D) ∧
      RVDefinablyEquivalent 𝓜 S₀.carrier N.carrier (gluedRVTags B (relativePositiveTags O D)) ∧
      ElementaryClassStep O hO power S₀ neg (objectClass 𝓜 S₀ ⟨_,A⟩)
        (objectClass 𝓜 S₀ ⟨_,Z⟩ + objectClass 𝓜 S₀ ⟨_,N⟩) := by
  have old (p : Fin h → RV0 O) (hp : p ∈ B) : ∃ a, RelativeRVWitness D G 0 a (rvTupleAssignment p) := by
    obtain ⟨a,_,v,_⟩ := valid p hp
    exact ⟨a,v⟩
  have gone (p : Fin h → RV0 O) (hp : p ∈ B) :
      ∃ b, RelativeRVWitness D (relativeDeleteLabelGraph j G) 0 b (rvTupleAssignment p) := by
    obtain ⟨_,b,_,v⟩ := valid p hp
    exact ⟨b,v⟩
  have pos (p : Fin h → RV0 O) (hp : p ∈ B) : ∃ b,
      RelativeRVWitness (relativePositiveTags O D) (relativePositiveGraph O j D G) 0 b (rvTupleAssignment p) := by
    obtain ⟨_,b,v,g⟩ := valid p hp
    exact ⟨b,relativePositiveGraph_valid O j v g⟩
  obtain ⟨A,arityA,tagA,graphA⟩ := gluedRVObject_exists sel defB defD defG headNonzero finiteBase old
  obtain ⟨Z,arityZ,tagZ,_⟩ := gluedRVObject_exists sel defB defD
    (relativeDeleteLabelGraph_definable j defG) headNonzero finiteBase gone
  obtain ⟨N,arityN,tagN,_⟩ := gluedRVObject_exists sel defB
    (relativePositiveTags_definable O neg defD) (relativePositiveGraph_definable O j neg defD defG)
    headNonzero finiteBase pos
  have isoA := rv_cast_carrier_equiv A arityA _ tagA
  have isoZ := rv_cast_carrier_equiv Z arityZ _ tagZ
  have isoN := rv_cast_carrier_equiv N arityN _ tagN
  let j₀ : Fin (t+k+1) := rvTail (a := t) (b := k+1) j
  have fin := gluedRV_finite_deletion j sel finiteBase (fun p hp w => (gone p hp).choose_spec.finite_fiber w)
    A arityA graphA
  let idx : Fin (A.arity+1) ≃ Fin A.arity ⊕ Fin 1 := finSumFinEquiv.symm
  let Z₀ := zeroBlowupObject A j₀ fin
  let N₀ := positiveBlowupObject O hO power S₀ A idx neg j₀ fin
  have eqZ : objectClass 𝓜 S₀ ⟨_,Z₀⟩ = objectClass 𝓜 S₀ ⟨_,Z⟩ := by
    apply scissors_sound 𝓜 S₀
    exact RVRelation.iso Z₀ Z (isoA.trans isoZ.symm)
  let mul := {s : Fin 1 → RV0 O | unsignedValue O (s 0) < 1 ∧ s 0 ≠ 0}
  have pad : RVDefinablyEquivalent 𝓜 S₀.carrier N₀.carrier (productSet A.carrier mul) :=
    (rv_reindex_equivalent 𝓜 S₀ idx _ (isRVSet_inter (isRVSet_precomp Sum.inl A.definable)
      (isRVSet_precomp Sum.inr (nonzero_multipliers_definable O hO power S₀ neg)))).symm
  have prod : RVDefinablyEquivalent 𝓜 S₀.carrier (productSet A.carrier mul) (productSet (gluedRVTags B D) mul) := by
    let e := Equiv.sumCongr (finCongr arityA.symm) (Equiv.refl (Fin 1))
    have f := rv_reindex_equivalent 𝓜 S₀ e (productSet A.carrier mul)
      (isRVSet_inter (isRVSet_precomp Sum.inl A.definable)
        (isRVSet_precomp Sum.inr (nonzero_multipliers_definable O hO power S₀ neg)))
    have eq : {y | y ∘ e.symm ∈ productSet A.carrier mul} = productSet (gluedRVTags B D) mul := by
      ext y
      exact and_congr ((tagA (y ∘ Sum.inl))) Iff.rfl
    rwa [eq] at f
  have eqN : objectClass 𝓜 S₀ ⟨_,N₀⟩ = objectClass 𝓜 S₀ ⟨_,N⟩ := by
    apply scissors_sound 𝓜 S₀
    exact RVRelation.iso N₀ N (pad.trans (prod.trans ((glued_positive_tags_equiv O hO power S₀ neg defB defD).trans isoN.symm)))
  have step := elementaryClassStep_of_blowup O hO power S₀ neg A j₀ idx fin 0
  change ElementaryClassStep O hO power S₀ neg (objectClass 𝓜 S₀ ⟨_,A⟩ + 0)
    (objectClass 𝓜 S₀ ⟨_,Z₀⟩ + objectClass 𝓜 S₀ ⟨_,N₀⟩ + 0) at step
  rw [eqZ,eqN,add_zero,add_zero] at step
  exact ⟨A,Z,N,isoA,isoZ,isoN,step⟩

end GeneralizedEuler.Section5
