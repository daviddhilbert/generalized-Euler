module

public import Section5.FieldOrderIsomorphisms
public import Section5.StandardHeadContractions

/-! A relatively unary bijection can be compared in any order whose
first coordinate is the one that moves. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv) {n k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem relativelyUnary_standard_outputs_commonBlowup
    (hyp : FieldwiseContractionHypotheses S)
    {A B : RetainedFieldFamily 𝓜 S (n+1) k}
    {order : Equiv.Perm (Fin (n+1))} (U : StandardHeadOutput A order) (V : StandardHeadOutput B order)
    (f : MixedGraphIso 𝓜 S
      {a : SortedAssignment Z (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.carrier}
      {b : SortedAssignment Z (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.carrier})
    (fixed : ∀ x i, i ≠ order 0 → (f.equiv x).val .vf i = x.val .vf i)
    (keep : ∀ x, (f.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select) :
    terminalCommonBlowup S neg U.terminal V.terminal U.tags V.tags := by
  obtain ⟨e,eval⟩ := RetainedFieldFamily.permuted_iso f order
  let p := (A.permuteVF_iso order).choose
  have tail (x) : (e.equiv x).val .vf ∘ Fin.succ = x.val .vf ∘ Fin.succ := by
    have ev := (A.permuteVF_iso order).choose_spec.1 (p.equiv.symm x)
    change (p.equiv (p.equiv.symm x)).val .vf = (p.equiv.symm x).val .vf ∘ order at ev
    rw [p.equiv.apply_symm_apply] at ev
    rw [(eval x).1,ev]
    funext i
    exact fixed (p.equiv.symm x) (order i.succ) (fun h => Fin.succ_ne_zero i (order.injective h))
  have selected (x) :
      (e.equiv x).val .rv ∘ (B.permuteVF order).select = x.val .rv ∘ (A.permuteVF order).select := by
    have ev := (A.permuteVF_iso order).choose_spec.2 (p.equiv.symm x)
    change (p.equiv (p.equiv.symm x)).val .rv = (p.equiv.symm x).val .rv at ev
    rw [p.equiv.apply_symm_apply] at ev
    rw [(eval x).2,ev]
    exact keep (p.equiv.symm x)
  obtain ⟨U',u,au,idxU⟩ := U
  obtain ⟨V',v,av,idxV⟩ := V
  cases u with
  | next H runH =>
    cases v with
    | next J runJ =>
      let : Finite H.target.tags := H.target.finiteTags
      let : Finite J.target.tags := J.target.finiteTags
      let ih : Fin (Nat.card H.target.tags) ≃ H.target.tags := (Finite.equivFin _).symm
      let ij : Fin (Nat.card J.target.tags) ≃ J.target.tags := (Finite.equivFin _).symm
      exact relativelyUnary_contraction_runs_commonBlowup S neg hyp H J ih ij runH runJ idxU idxV e tail selected

end GeneralizedEuler.Section5
