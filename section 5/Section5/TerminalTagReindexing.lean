module

public import Section5.FieldwiseContractionRelations
import all Section4.Objects

/-! The terminal graded class depends on the retained labels and the
carrier. Changing the enumeration of all RV tags preserves the class. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {k a b : ℕ}

theorem RetainedFieldFamily.terminalGradedClass_reindex
    (A : RetainedFieldFamily M S 0 k) (idx : Fin a ≃ A.tags) (idy : Fin b ≃ A.tags)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0)) :
    A.terminalGradedClass idx zero hz = A.terminalGradedClass idy zero hz := by
  apply Finset.sum_congr rfl
  intro s _
  let U := (A.terminalGradedPiece idx s zero hz).2
  let V := (A.terminalGradedPiece idy s zero hz).2
  let p := idy.trans idx.symm
  have iso := rv_reindex_equivalent M S p U.carrier U.definable
  have same : {x : Fin b → RV0 O | x ∘ p.symm ∈ U.carrier} = V.carrier := by
    ext x
    have eq : (x ∘ p.symm) ∘ idx.symm = x ∘ idy.symm := by
      funext i
      simp [p,Function.comp_apply]
    have sel (i : Fin k) : (x ∘ p.symm) (A.terminalSelect idx i) = x (A.terminalSelect idy i) :=
      congrFun eq (A.select i)
    refine (A.terminalGradedPiece_mem idx s zero hz (x ∘ p.symm)).trans (Iff.trans ?_
      (A.terminalGradedPiece_mem idy s zero hz x).symm)
    refine and_congr ?_ (forall_congr' fun i => iff_congr (not_congr (congrArg (· = zero.val) (sel i)).to_iff) Iff.rfl)
    change (Fin.elim0,(x ∘ p.symm) ∘ idx.symm) ∈ A.carrier ↔ (Fin.elim0,x ∘ idy.symm) ∈ A.carrier
    rw [eq]
  have toV : RVDefinablyEquivalent M S.carrier U.carrier V.carrier := same ▸ iso
  exact scissors_sound M S (.iso U V toV)

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S₀.carrier .rv) {c d : ℕ}

theorem terminalCommonBlowup_reindex
    {A B : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S₀ 0 k}
    (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags) (idyA : Fin c ≃ A.tags) (idyB : Fin d ≃ B.tags)
    (h : terminalCommonBlowup S₀ neg A B idxA idxB) : terminalCommonBlowup S₀ neg A B idyA idyB := by
  unfold terminalCommonBlowup at h ⊢
  rwa [A.terminalGradedClass_reindex idxA idyA (baseRVZero S₀) rfl,
    B.terminalGradedClass_reindex idxB idyB (baseRVZero S₀) rfl] at h

end Canonical

end GeneralizedEuler.Section5
