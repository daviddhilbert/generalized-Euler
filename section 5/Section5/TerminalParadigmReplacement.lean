module

public import Section5.TerminalGradedIsomorphism

/-! Replacing a recorded paradigm by another definable paradigm
does not change a graded class when the zero patterns agree. All
other RV data remain fixed. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {m k : ℕ} {T : Type}

local notation "Z" => CanonicalSort O

theorem RetainedFieldFamily.terminalGradedClass_replace_paradigm
    (A B : RetainedFieldFamily M S 0 k) (idx : Fin m ≃ A.tags) (idy : Fin m ≃ B.tags)
    (mark : Fin m) (read : T → Fin m) (sep : ∀ j, read j ≠ mark)
    (t r : (T → RV0 O) → RV0 O)
    (defR : DefinableRelation M S.carrier (fun
      (x : SortedAssignment Z (RVVariables T))
      (y : SortedAssignment Z (RVVariables (Fin 1))) => r (x .rv) = y .rv 0))
    (P : (Fin m → RV0 O) → Prop)
    (stable : ∀ q (v : RV0 O), P (Function.update q mark v) ↔ P q)
    (left : ∀ q, q ∈ A.terminalLabels idx ↔ P q ∧ q mark = t (q ∘ read))
    (right : ∀ q, q ∈ B.terminalLabels idy ↔ P q ∧ q mark = r (q ∘ read))
    (sel : A.terminalSelect idx = B.terminalSelect idy)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (sameZero : ∀ q, P q → (t (q ∘ read) = zero.val ↔ r (q ∘ read) = zero.val)) :
    A.terminalGradedClass idx zero hz = B.terminalGradedClass idy zero hz := by
  classical
  have keep (q : Fin m → RV0 O) (v : RV0 O) : Function.update q mark v ∘ read = q ∘ read := by
    funext j
    exact Function.update_of_ne (sep j) _ _
  let send (q : Fin m → RV0 O) := Function.update q mark (r (q ∘ read))
  let back (q : Fin m → RV0 O) := Function.update q mark (t (q ∘ read))
  have readSend (q : Fin m → RV0 O) : send q ∘ read = q ∘ read := keep q _
  have readBack (q : Fin m → RV0 O) : back q ∘ read = q ∘ read := keep q _
  let e : A.terminalLabels idx ≃ B.terminalLabels idy :=
    { toFun := fun q => ⟨send q.val,(right _).2 ⟨(stable _ _).2 ((left _).1 q.property).1,
        (Function.update_self _ _ _).trans (congrArg r (readSend q.val).symm)⟩⟩
      invFun := fun q => ⟨back q.val,(left _).2 ⟨(stable _ _).2 ((right _).1 q.property).1,
        (Function.update_self _ _ _).trans (congrArg t (readBack q.val).symm)⟩⟩
      left_inv := fun q => Subtype.ext (funext fun j => by
        by_cases h : j = mark
        · subst j
          exact (show back (send q.val) mark = t (send q.val ∘ read) from Function.update_self _ _ _).trans
            ((congrArg t (readSend q.val)).trans ((left _).1 q.property).2.symm)
        · exact (Function.update_of_ne h _ _).trans (Function.update_of_ne h _ _))
      right_inv := fun q => Subtype.ext (funext fun j => by
        by_cases h : j = mark
        · subst j
          exact (show send (back q.val) mark = r (back q.val ∘ read) from Function.update_self _ _ _).trans
            ((congrArg r (readBack q.val)).trans ((right _).1 q.property).2.symm)
        · exact (Function.update_of_ne h _ _).trans (Function.update_of_ne h _ _)) }
  let V := RVVariables (Fin m ⊕ Fin m)
  let take : (s : TCsort) → SumVariables (RVVariables T) (RVVariables (Fin 1)) s → V s
    | .vf => Sum.elim PEmpty.elim PEmpty.elim
    | .rv => Sum.elim (Sum.inl ∘ read) (fun _ => .inr mark)
  let past : (s : TCsort) → RVVariables (Fin m) s → V s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  have src := (A.terminalLabels_definable idx).pullback_relabel past
  have record := SortedDefinableOver.iInter (fun i : {j : Fin m // j ≠ mark} =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V) .rv (.inl i.val) (.inr i.val))
  have defR' := defR
  unfold DefinableRelation at defR'
  have graph : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)) := by
    convert src.inter ((defR'.pullback_relabel take).inter record) using 1
    ext a
    let l := a .rv ∘ Sum.inl
    let r' := a .rv ∘ Sum.inr
    simp only [Set.mem_inter_iff,Set.mem_iInter,Subtype.forall]
    change (∃ q : A.terminalLabels idx, q.val = l ∧ send q.val = r') ↔
      l ∈ A.terminalLabels idx ∧ r (l ∘ read) = r' mark ∧ ∀ i ≠ mark, l i = r' i
    constructor
    · rintro ⟨q,hq,e⟩
      refine ⟨hq ▸ q.property,?_⟩
      constructor
      · have val : send q.val mark = r (q.val ∘ read) := Function.update_self _ _ _
        exact (congrArg (fun w => r (w ∘ read)) hq).symm.trans (val.symm.trans (congrFun e mark))
      · intro i hi
        exact (congrFun hq i).symm.trans ((Function.update_of_ne hi _ _).symm.trans (congrFun e i))
    · rintro ⟨h,atMark,atOther⟩
      refine ⟨⟨l,h⟩,rfl,?_⟩
      funext i
      by_cases hi : i = mark
      · subst i
        exact (Function.update_self _ _ _).trans atMark
      · exact (Function.update_of_ne hi _ _).trans (atOther i hi)
  apply A.terminalGradedClass_of_label_iso B idx idy e graph (Equiv.refl _) zero hz
  intro q i
  change q.val (A.terminalSelect idx i) ≠ zero.val ↔ send q.val (B.terminalSelect idy i) ≠ zero.val
  rw [← sel]
  by_cases h : A.terminalSelect idx i = mark
  · rw [h,((left _).1 q.property).2]
    have e' : send q.val mark = r (q.val ∘ read) := Function.update_self _ _ _
    rw [e']
    exact not_congr (sameZero q.val ((left _).1 q.property).1)
  · exact (congrArg (· ≠ zero.val) (Function.update_of_ne h _ _)).to_iff.symm

end GeneralizedEuler.Section5
