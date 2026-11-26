module

public import Section5.UnaryTerminalSupports
public import Section5.UnaryGradedClassComparison
import all Section4.Objects

/-! A definable bijection of terminal labels gives exact equality of
graded classes when it preserves the selected zero pattern up to a
permutation. The values of the nonzero coordinates may change. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {k a b : ℕ}

theorem RetainedFieldFamily.terminalGradedClass_of_label_iso
    (A B : RetainedFieldFamily M S 0 k) (idx : Fin a ≃ A.tags) (idy : Fin b ≃ B.tags)
    (e : A.terminalLabels idx ≃ B.terminalLabels idy)
    (graph : SortedDefinableOver M S.carrier (rvGraph fun t => (e t).val))
    (order : Equiv.Perm (Fin k))
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (preserved : ∀ t : A.terminalLabels idx, ∀ i,
      t.val (A.terminalSelect idx i) ≠ zero.val ↔ (e t).val (B.terminalSelect idy (order i)) ≠ zero.val) :
    A.terminalGradedClass idx zero hz = B.terminalGradedClass idy zero hz := by
  let supports := order.finsetCongr
  let U (s : Finset (Fin k)) := A.terminalGradedPiece idx s zero hz
  let V (s : Finset (Fin k)) := B.terminalGradedPiece idy s zero hz
  have each (s : Finset (Fin k)) : objectClass M S (U s) = objectClass M S (V (supports s)) := by
    have count : (V (supports s)).1 = (U s).1 := by
      change Fintype.card {i // i ∈ supports s} = Fintype.card {i // i ∈ s}
      rw [Fintype.card_coe,Fintype.card_coe]
      exact Finset.card_map _
    let P (t : Fin a → RV0 O) := ∀ i, t (A.terminalSelect idx i) ≠ zero.val ↔ i ∈ s
    let Q (t : Fin b → RV0 O) := ∀ i, t (B.terminalSelect idy i) ≠ zero.val ↔ i ∈ supports s
    have left : (U s).2.carrier = {t ∈ A.terminalLabels idx | P t} :=
      Set.ext (A.terminalGradedPiece_mem idx s zero hz)
    have right : (V (supports s)).2.carrier = {t ∈ B.terminalLabels idy | Q t} :=
      Set.ext (B.terminalGradedPiece_mem idy (supports s) zero hz)
    have cut (t : A.terminalLabels idx) : P t.val ↔ Q (e t).val := by
      have support (i : Fin k) : order i ∈ supports s ↔ i ∈ s := by
        change order i ∈ Finset.map order.toEmbedding s ↔ _
        rw [Finset.mem_map_equiv,order.symm_apply_apply]
      constructor
      · intro h j
        obtain ⟨i,rfl⟩ := order.surjective j
        exact (preserved t i).symm.trans ((h i).trans (support i).symm)
      · intro h i
        exact (preserved t i).trans ((h (order i)).trans (support i))
    have definable : isRVSet M S {t ∈ A.terminalLabels idx | P t} := left ▸ (U s).2.definable
    have iso : RVDefinablyEquivalent M S.carrier (U s).2.carrier (V (supports s)).2.carrier := by
      rw [left,right]
      exact rvDefinableEquiv_of_preserved_cut (M := M) (S := S) e graph P Q cut definable
    have graded {p q : ℕ} (C : RVObject M S p) (D : RVObject M S q) (eq : q = p)
        (h : RVDefinablyEquivalent M S.carrier C.carrier D.carrier) :
        objectClass M S ⟨p,C⟩ = objectClass M S ⟨q,D⟩ := by
      subst q
      exact scissors_sound M S (.iso C D h)
    exact graded (U s).2 (V (supports s)).2 count iso
  exact Fintype.sum_equiv supports (fun s => objectClass M S (U s)) (fun s => objectClass M S (V s)) each

end GeneralizedEuler.Section5
