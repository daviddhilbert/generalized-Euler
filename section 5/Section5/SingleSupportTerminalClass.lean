module

public import Section5.TerminalGradedIsomorphism
import all Section4.Objects

/-! If every terminal label has one specified support, its entire
graded class is the class of the corresponding RV carrier. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {a k d : ℕ}

theorem RetainedFieldFamily.terminalGradedClass_of_single_support
    (A : RetainedFieldFamily M S 0 k) (idx : Fin a ≃ A.tags)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (s : Finset (Fin k)) (deg : s.card = d)
    (support : ∀ t ∈ A.terminalLabels idx, ∀ i, t (A.terminalSelect idx i) ≠ zero.val ↔ i ∈ s)
    (U : RVObject M S d)
    (iso : RVDefinablyEquivalent M S.carrier (A.terminalLabels idx) U.carrier) :
    A.terminalGradedClass idx zero hz = objectClass M S ⟨d,U⟩ := by
  classical
  let P (t : Finset (Fin k)) := A.terminalGradedPiece idx t zero hz
  have vanish (t : Finset (Fin k)) (ne : t ≠ s) : objectClass M S (P t) = 0 := by
    have empty : (P t).2.carrier = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro a ha
      obtain ⟨mem,hs⟩ := (A.terminalGradedPiece_mem idx t zero hz a).1 ha
      exact ne (Finset.ext fun i => (hs i).symm.trans (support a mem i))
    exact scissors_sound M S (.zero (P t).2 empty)
  have one : objectClass M S (P s) = objectClass M S ⟨d,U⟩ := by
    have eq : (P s).2.carrier = A.terminalLabels idx := by
      ext a
      exact (A.terminalGradedPiece_mem idx s zero hz a).trans
        ⟨And.left,fun h => ⟨h,support a h⟩⟩
    have graded {p q : ℕ} (V : RVObject M S p) (W : RVObject M S q) (e : p = q)
        (h : RVDefinablyEquivalent M S.carrier V.carrier W.carrier) :
        objectClass M S ⟨p,V⟩ = objectClass M S ⟨q,W⟩ := by
      subst q
      exact scissors_sound M S (.iso V W h)
    apply graded (P s).2 U (by simpa only [P, terminalGradedPiece, Fintype.card_coe] using deg)
    rwa [eq]
  unfold terminalGradedClass
  rw [Finset.sum_eq_single s (fun t _ h => vanish t h) (fun h => (h (Finset.mem_univ _)).elim)]
  exact one

end GeneralizedEuler.Section5
