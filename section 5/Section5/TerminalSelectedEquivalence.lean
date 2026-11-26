module

public import Section5.TerminalTagReindexing
import all Section4.Objects

/-! Reordering the selected coordinates permutes the zero patterns.
Each piece keeps its degree and the same underlying RV carrier
after the corresponding tag reindexing. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {k a b : ℕ}

theorem RetainedFieldFamily.terminalGradedClass_selected_equiv
    (A B : RetainedFieldFamily M S 0 k) (tags : A.tags ≃ B.tags)
    (idx : Fin a ≃ A.tags) (idy : Fin b ≃ B.tags)
    (order : Equiv.Perm (Fin k))
    (eqTags : ∀ t : A.tags → RV0 O, (Fin.elim0,t) ∈ A.carrier ↔ (Fin.elim0,t ∘ tags.symm) ∈ B.carrier)
    (selected : ∀ i, tags (A.select i) = B.select (order i))
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0)) :
    A.terminalGradedClass idx zero hz = B.terminalGradedClass idy zero hz := by
  let via := idx.trans tags
  have reorder : B.terminalGradedClass via zero hz = B.terminalGradedClass idy zero hz :=
    B.terminalGradedClass_reindex via idy zero hz
  refine Eq.trans ?_ reorder
  let supports := order.finsetCongr
  let U (s : Finset (Fin k)) := A.terminalGradedPiece idx s zero hz
  let V (s : Finset (Fin k)) := B.terminalGradedPiece via s zero hz
  have each (s : Finset (Fin k)) : objectClass M S (U s) = objectClass M S (V (supports s)) := by
    have count : (V (supports s)).1 = (U s).1 := by
      change Fintype.card {i // i ∈ supports s} = Fintype.card {i // i ∈ s}
      rw [Fintype.card_coe,Fintype.card_coe]
      exact Finset.card_map _
    have same : (U s).2.carrier = (V (supports s)).2.carrier := by
      ext x
      have hU := A.terminalGradedPiece_mem idx s zero hz x
      have hV := B.terminalGradedPiece_mem via (supports s) zero hz x
      refine hU.trans (Iff.trans ?_ hV.symm)
      refine and_congr (eqTags (x ∘ idx.symm)) ?_
      have read (i : Fin k) : (B.terminalSelect via) (order i) = (A.terminalSelect idx) i := by
        change idx.symm (tags.symm (B.select (order i))) = idx.symm (A.select i)
        rw [← selected,tags.symm_apply_apply]
      have support (i : Fin k) : order i ∈ supports s ↔ i ∈ s := by
        change order i ∈ Finset.map order.toEmbedding s ↔ _
        rw [Finset.mem_map_equiv,order.symm_apply_apply]
      constructor
      · intro h j
        obtain ⟨i,rfl⟩ := order.surjective j
        exact (congrArg (fun q => x q ≠ zero.val) (read i)).to_iff.trans ((h i).trans (support i).symm)
      · intro h i
        exact (congrArg (fun q => x q ≠ zero.val) (read i)).to_iff.symm.trans ((h (order i)).trans (support i))
    have iso : RVDefinablyEquivalent M S.carrier (U s).2.carrier (V (supports s)).2.carrier := by
      rw [same]
      exact ⟨Equiv.refl _,definable_identity_label M S (V (supports s)).2.definable⟩
    have graded {p q : ℕ} (C : RVObject M S p) (D : RVObject M S q) (eq : q = p)
        (h : RVDefinablyEquivalent M S.carrier C.carrier D.carrier) :
        objectClass M S ⟨p,C⟩ = objectClass M S ⟨q,D⟩ := by
      subst q
      exact scissors_sound M S (.iso C D h)
    exact graded (U s).2 (V (supports s)).2 count iso
  exact Fintype.sum_equiv supports (fun s => objectClass M S (U s)) (fun s => objectClass M S (V s)) each

end GeneralizedEuler.Section5
