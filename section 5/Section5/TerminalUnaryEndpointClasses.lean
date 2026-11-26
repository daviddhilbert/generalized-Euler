module

public import Section5.TerminalUnaryRows
public import Section5.HeadPatternIndices
public import Section5.GluedRowCoordinateGraphs

/-! The glued terminal rows are the ordinary terminal objects on the
two patterns extending the old support. Appending the retained tuple
to the tags is a definable coordinate embedding. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder RelativeObjectFamily

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {a k t : ℕ}

@[expose] def terminalUnaryKeep (keep : Fin t → Fin k) (new : Bool) : Fin (t+new.toNat) → Fin (k+1) :=
  Sum.elim (Fin.castSucc ∘ keep) (fun _ => Fin.last k) ∘ finSumFinEquiv.symm

theorem castSucc_mem_terminalUnaryKeep (keep : Fin t → Fin k) (new : Bool) (i : Fin k) :
    i.castSucc ∈ Set.range (terminalUnaryKeep keep new) ↔ i ∈ Set.range keep := by
  constructor
  · rintro ⟨j,eq⟩
    cases h : finSumFinEquiv.symm j with
    | inl l =>
      change Sum.elim (Fin.castSucc ∘ keep) (fun _ => Fin.last k) (finSumFinEquiv.symm j) = i.castSucc at eq
      rw [h] at eq
      exact ⟨l,Fin.castSucc_injective _ eq⟩
    | inr l =>
      change Sum.elim (Fin.castSucc ∘ keep) (fun _ => Fin.last k) (finSumFinEquiv.symm j) = i.castSucc at eq
      rw [h] at eq
      exact False.elim (Fin.castSucc_ne_last i eq.symm)
  · rintro ⟨j,rfl⟩
    exact ⟨finSumFinEquiv (.inl j),by simp [terminalUnaryKeep]⟩

theorem last_mem_terminalUnaryKeep (keep : Fin t → Fin k) (new : Bool) :
    Fin.last k ∈ Set.range (terminalUnaryKeep keep new) ↔ new = true := by
  constructor
  · rintro ⟨j,eq⟩
    cases h : finSumFinEquiv.symm j with
    | inl l =>
      change Sum.elim (Fin.castSucc ∘ keep) (fun _ => Fin.last k) (finSumFinEquiv.symm j) = Fin.last k at eq
      rw [h] at eq
      exact False.elim (Fin.castSucc_ne_last (keep l) eq)
    | inr l =>
      cases new
      · exact l.elim0
      · rfl
  · rintro rfl
    exact ⟨finSumFinEquiv (.inr ⟨0,by decide⟩),by simp [terminalUnaryKeep]⟩

namespace RetainedFieldFamily

variable (B : RetainedFieldFamily M S 0 (k+1)) (tags : Fin a ≃ B.tags) (keep : Fin t → Fin k)
  (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))

theorem terminalUnaryPiece_mem (new : Bool) (x : Fin a → RV0 O) :
    x ∈ (B.terminalPiece tags (terminalUnaryKeep keep new) zero hz).carrier ↔
      x ∈ B.terminalLabels tags ∧
      (∀ i : Fin k, x (B.terminalOldHead tags i) ≠ zero.val ↔ i ∈ Set.range keep) ∧
      (x (B.terminalNewLead tags) ≠ zero.val ↔ new = true) := by
  change (x ∈ B.terminalLabels tags ∧
    ∀ i, x (B.terminalSelect tags i) ≠ zero.val ↔ i ∈ Set.range (terminalUnaryKeep keep new)) ↔ _
  apply and_congr_right
  intro _
  constructor
  · intro all
    exact ⟨fun i => (all i.castSucc).trans (castSucc_mem_terminalUnaryKeep keep new i),
      (all (Fin.last k)).trans (last_mem_terminalUnaryKeep keep new)⟩
  · rintro ⟨old,last⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact last.trans (last_mem_terminalUnaryKeep keep new).symm
    · exact (old j).trans (castSucc_mem_terminalUnaryKeep keep new j).symm

set_option maxHeartbeats 600000 in
theorem terminalUnaryRows_gluedClass (b₀ b₁ : ℕ)
    (v : ∀ p : SortedAssignment (CanonicalSort O) (RVVariables (Fin k)), Valid (B.terminalUnaryRows tags zero b₀ b₁) zero p) :
    let I := oldHeadPatternIndex keep zero hz
    gluedClass zero hz I (B.terminalUnaryRows tags zero b₀ b₁) (fun p _ => v (rvTupleAssignment p)) =
      objectClass M S ⟨t,B.terminalPiece tags (terminalUnaryKeep keep false) zero hz⟩ +
      objectClass M S ⟨t+1,B.terminalPiece tags (terminalUnaryKeep keep true) zero hz⟩ := by
  intro I
  let U := B.terminalUnaryRows tags zero b₀ b₁
  let Z := B.terminalPiece tags (terminalUnaryKeep keep false) zero hz
  let N := B.terminalPiece tags (terminalUnaryKeep keep true) zero hz
  let D (i : Fin 2) := (U i).row zero hz I (fun p _ => v (rvTupleAssignment p) i)
  have lower : (D 0).gluedClass = objectClass M S ⟨t,Z⟩ := by
    apply (D 0).gluedClass_eq_of_projection Z rfl (B.terminalOldHead tags)
    intro p x
    change ((True ∧ ∀ i, p i ≠ zero.val ↔ i ∈ Set.range keep) ∧
      (x ∈ B.terminalLabels tags ∧ x ∘ B.terminalOldHead tags = p) ∧ x (B.terminalNewLead tags) = zero.val) ↔
      x ∈ Z.carrier ∧ p = x ∘ B.terminalOldHead tags
    simp only [true_and]
    have mem : x ∈ Z.carrier ↔ x ∈ B.terminalLabels tags ∧
        (∀ i : Fin k, x (B.terminalOldHead tags i) ≠ zero.val ↔ i ∈ Set.range keep) ∧
        (x (B.terminalNewLead tags) ≠ zero.val ↔ false = true) :=
      B.terminalUnaryPiece_mem tags keep zero hz false x
    rw [mem]
    constructor
    · rintro ⟨hp,⟨hx,rfl⟩,last⟩
      exact ⟨⟨hx,hp,by simp [last]⟩,rfl⟩
    · rintro ⟨⟨hx,hp,last⟩,rfl⟩
      exact ⟨hp,⟨hx,rfl⟩,not_ne_iff.1 (fun hn => Bool.false_ne_true (last.1 hn))⟩
  have upper : (D 1).gluedClass = objectClass M S ⟨t+1,N⟩ := by
    apply (D 1).gluedClass_eq_of_projection N rfl (B.terminalOldHead tags)
    intro p x
    change ((True ∧ ∀ i, p i ≠ zero.val ↔ i ∈ Set.range keep) ∧
      (x ∈ B.terminalLabels tags ∧ x ∘ B.terminalOldHead tags = p) ∧ x (B.terminalNewLead tags) ≠ zero.val) ↔
      x ∈ N.carrier ∧ p = x ∘ B.terminalOldHead tags
    simp only [true_and]
    have mem : x ∈ N.carrier ↔ x ∈ B.terminalLabels tags ∧
        (∀ i : Fin k, x (B.terminalOldHead tags i) ≠ zero.val ↔ i ∈ Set.range keep) ∧
        (x (B.terminalNewLead tags) ≠ zero.val ↔ true = true) :=
      B.terminalUnaryPiece_mem tags keep zero hz true x
    rw [mem]
    constructor
    · rintro ⟨hp,⟨hx,rfl⟩,last⟩
      exact ⟨⟨hx,hp,iff_of_true last rfl⟩,rfl⟩
    · rintro ⟨⟨hx,hp,last⟩,rfl⟩
      exact ⟨hp,⟨hx,rfl⟩,last.2 rfl⟩
  change (∑ i : Fin 2, (D i).gluedClass) = objectClass M S ⟨t,Z⟩ + objectClass M S ⟨t+1,N⟩
  rw [Fin.sum_univ_two,lower,upper]

end RetainedFieldFamily

end GeneralizedEuler.Section5
