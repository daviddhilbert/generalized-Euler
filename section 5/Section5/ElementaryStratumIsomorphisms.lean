module

public import Section5.ElementaryLiftStrata
public import Section5.PaddedFieldLift

/-! Definably remove the dummy coordinates of the zero stratum and
reindex the positive stratum in the elementary blowup lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k m : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1))
  (j : Fin (k+1))
  (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite)

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "W" => ElementaryLiftVars O hO power S U

@[expose] def elementaryZeroStratum : Set (SortedAssignment (CanonicalSort O) W) :=
  {w | w ∈ elementaryLiftCarrier O hO power S U j ∧ w .rv (.inr ()) = 0}

@[expose] def elementaryNonzeroStratum : Set (SortedAssignment (CanonicalSort O) W) :=
  {w | w ∈ elementaryLiftCarrier O hO power S U j ∧ w .rv (.inr ()) ≠ 0}

@[expose] def elementaryZeroIndices :
    ∀ s, ObjectLift.Vars (zeroBlowupObject U j finiteDelete) s → W s
  | .vf => j.succAbove
  | .rv => Sum.inl

include finiteDelete in
theorem elementaryZeroStratum_definable :
    SortedDefinableOver 𝓜 S.carrier (elementaryZeroStratum O hO power S U j) := by
  let Z := zeroBlowupObject U j finiteDelete
  let pos := elementaryZeroIndices O hO power S U j finiteDelete
  have base := (ObjectLift.definable Z).pullback_relabel pos
  have fieldZero := field_eq_zero_definable O hO power S (V := W) j
  have rvZero := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := W)
    .rv (.inr ()) rvZeroTerm
  convert base.inter (fieldZero.inter rvZero) using 1
  ext a
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,realize_rvZeroTerm O hO power]
  exact elementary_zero_iff_padded_lift O hO power S U j finiteDelete a

theorem elementaryZeroStratum_iso :
    MixedDefinablyEquivalent 𝓜 S (elementaryZeroStratum O hO power S U j)
      (ObjectLift.carrier (zeroBlowupObject U j finiteDelete)) := by
  let Z := zeroBlowupObject U j finiteDelete
  let p := elementaryZeroIndices O hO power S U j finiteDelete
  let Y := elementaryZeroStratum O hO power S U j
  apply mixed_projection_equivalent p Y (ObjectLift.carrier Z)
    (elementaryZeroStratum_definable O hO power S U j finiteDelete)
  have mem (a : SortedAssignment (CanonicalSort O) W) :
      a ∈ Y ↔ (fun s => a s ∘ p s) ∈ ObjectLift.carrier Z ∧ a .vf j = 0 ∧ a .rv (.inr ()) = 0 :=
    elementary_zero_iff_padded_lift O hO power S U j finiteDelete a
  refine ⟨fun a ha => ((mem a).1 ha).1,?_,?_⟩
  · intro a ha b hb eq
    have h := (mem a).1 ha
    have g := (mem b).1 hb
    funext s i
    cases s with
    | vf =>
      by_cases e : i = j
      · subst i
        exact h.2.1.trans g.2.1.symm
      · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq e
        exact congrFun (congrFun eq .vf) l
    | rv => cases i with
      | inl l => exact congrFun (congrFun eq .rv) l
      | inr l =>
        cases l
        exact h.2.2.trans g.2.2.symm
  · intro a ha
    let b : SortedAssignment (CanonicalSort O) W
      | .vf => Fin.insertNth (α := fun _ => K) j 0 (a .vf)
      | .rv => Sum.elim (a .rv) (fun _ => 0)
    have eq : (fun s => b s ∘ p s) = a := by
      funext s i
      cases s with
      | vf => exact Fin.insertNth_apply_succAbove _ _ _ _
      | rv => rfl
    refine ⟨b,(mem b).2 ⟨eq.symm ▸ ha,?_ ,rfl⟩,eq⟩
    exact Fin.insertNth_apply_same _ _ _

def finOneUnit : Fin 1 ≃ Unit where
  toFun _ := ()
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

theorem elementaryNonzeroStratum_definable_and_iso
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv) :
    let P := positiveBlowupObject O hO power S U idx hneg j finiteDelete
    SortedDefinableOver 𝓜 S.carrier (elementaryNonzeroStratum O hO power S U j) ∧
    MixedDefinablyEquivalent 𝓜 S (elementaryNonzeroStratum O hO power S U j) (ObjectLift.carrier P) := by
  intro P
  let p : ∀ s, ObjectLift.Vars P s ≃ W s
    | .vf => Equiv.refl _
    | .rv => idx.trans (Equiv.sumCongr (Equiv.refl _) finOneUnit)
  have eq : elementaryNonzeroStratum O hO power S U j =
      {a | (fun s => a s ∘ p s) ∈ ObjectLift.carrier P} := by
    ext a
    exact elementary_nonzero_iff_lift O hO power S U j finiteDelete idx hneg a
  have defA := (ObjectLift.definable P).pullback_relabel (fun s => (p s : _ → _))
  have iso := mixed_reindex_equivalent (fun s => (p s).symm) (ObjectLift.carrier P) (ObjectLift.definable P)
  rw [eq]
  exact ⟨defA,iso.symm⟩

end GeneralizedEuler.Section5
