module

public import Section5.FieldRVFiberRows
public import Section5.NestedGeneratedBases
import all Section4.Objects

/-! A terminal class depends on the carrier of the tags and the
selected coordinates. Rewriting an equality of generated bases
keeps this data. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S T : SortedSubstructure M}
  {n k a : ℕ}

namespace RetainedFieldFamily

@[expose] def rebaseEq (A : RetainedFieldFamily M S n k) (e : S = T) :
    RetainedFieldFamily M T n k where
  tags := A.tags
  finiteTags := A.finiteTags
  select := A.select
  carrier := A.carrier
  definable := e ▸ A.definable
  finiteFibers := A.finiteFibers

theorem terminalGradedClass_congr
    (A B : RetainedFieldFamily M S 0 k) (idxA : Fin a ≃ A.tags) (idxB : Fin a ≃ B.tags)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (tags : A.terminalLabels idxA = B.terminalLabels idxB) (sel : A.terminalSelect idxA = B.terminalSelect idxB) :
    A.terminalGradedClass idxA zero hz = B.terminalGradedClass idxB zero hz := by
  apply Finset.sum_congr rfl
  intro s _
  let U := (A.terminalGradedPiece idxA s zero hz).2
  let V := (B.terminalGradedPiece idxB s zero hz).2
  have eq : U.carrier = V.carrier := by
    ext x
    have e := A.terminalGradedPiece_mem idxA s zero hz x
    have f := B.terminalGradedPiece_mem idxB s zero hz x
    exact e.trans ((by rw [tags,sel] : (_ ∧ _) ↔ (_ ∧ _)).trans f.symm)
  apply scissors_sound M S
  apply RVRelation.iso
  change RVDefinablyEquivalent M S.carrier U.carrier V.carrier
  rw [eq]
  exact ⟨Equiv.refl _,definable_identity_label M S V.definable⟩

theorem terminalGradedClass_rebaseEq (A : RetainedFieldFamily M S 0 k) (e : S = T)
    (idx : Fin a ≃ A.tags) (zero : S.carrier .rv)
    (hz : zero.val = M.funMap .rvZero (fun j => j.elim0)) :
    (A.rebaseEq e).terminalGradedClass idx (e ▸ zero) (by cases e; exact hz) =
      (e ▸ A.terminalGradedClass idx zero hz : RVSemiring M T) := by
  cases e
  rfl

end RetainedFieldFamily

end GeneralizedEuler.Section5
