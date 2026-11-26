module

public import Section5.TwoHeadRefinements
public import Section5.PositionedTailContractions
public import Section5.TerminalParadigmReplacement

/-! An output with a recorded paradigm and a prepared unary domain
can be compared by replacing only its paradigm coordinate. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

@[expose] def positionedPairSelect {k ℓ : ℕ} {I : Type} (select : Fin k → I) :
    Fin (k+2) → HistoryIndex ℓ ⊕ (Unit ⊕ I) :=
  Fin.lastCases (Sum.inl (lastIndex ℓ))
    (Fin.lastCases (Sum.inr (.inl ())) (Sum.inr ∘ Sum.inr ∘ select))

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {k ℓ : ℕ} {I : Type}

structure PositionedTwoHeadOutput (A : RetainedFieldFamily M S 2 k)
    (domain : Set (K × (I → RV0 O))) (select : Fin k → I)
    (paradigm : (I → RV0 O) → RV0 O)
    (P : UnaryPreparation O (PreparationLabels O (RV0 O) ℓ)) where
  setup : TwoHeadRefinement A
  pack : HistoryIndex ℓ ⊕ (Unit ⊕ I) ≃ setup.second.target.tags
  select_eq : ∀ i, setup.second.target.select i = pack (positionedPairSelect select i)
  labels : ∀ t : HistoryIndex ℓ ⊕ (Unit ⊕ I) → RV0 O,
    (Fin.elim0,t ∘ pack.symm) ∈ setup.second.target.carrier ↔
      (∃ x, (x,t ∘ Sum.inr ∘ Sum.inr) ∈ domain ∧
        P.label x = decodeHistory O ℓ (t ∘ Sum.inl)) ∧
      t (.inr (.inl ())) = paradigm (t ∘ Sum.inr ∘ Sum.inr)

local notation "Z" => CanonicalSort O

theorem PositionedTwoHeadOutput.terminal_class_eq
    {A B : RetainedFieldFamily M S 2 k}
    {D : Set (K × (I → RV0 O))} {select : Fin k → I}
    {P : UnaryPreparation O (PreparationLabels O (RV0 O) ℓ)}
    {t r : (I → RV0 O) → RV0 O}
    (U : PositionedTwoHeadOutput A D select t P) (V : PositionedTwoHeadOutput B D select r P)
    (defR : DefinableRelation M S.carrier (fun (a : SortedAssignment Z (RVVariables I))
      (b : SortedAssignment Z (RVVariables (Fin 1))) => r (a .rv) = b .rv 0))
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (sameZero : ∀ p, t p = zero.val ↔ r p = zero.val) :
    U.setup.second.target.terminalGradedClass U.setup.enumerate zero hz =
      V.setup.second.target.terminalGradedClass V.setup.enumerate zero hz := by
  let T := HistoryIndex ℓ ⊕ (Unit ⊕ I)
  let : Finite U.setup.second.target.tags := U.setup.second.target.finiteTags
  let : Finite T := Finite.of_equiv _ U.pack.symm
  let p : Fin (Nat.card T) ≃ T := (Finite.equivFin _).symm
  let idx := p.trans U.pack
  let idy := p.trans V.pack
  rw [U.setup.second.target.terminalGradedClass_reindex U.setup.enumerate idx zero hz,
    V.setup.second.target.terminalGradedClass_reindex V.setup.enumerate idy zero hz]
  let mark := p.symm (.inr (.inl ()))
  let read : I → Fin (Nat.card T) := p.symm ∘ Sum.inr ∘ Sum.inr
  let test (q : Fin (Nat.card T) → RV0 O) :=
    ∃ x, (x,q ∘ read) ∈ D ∧ P.label x = decodeHistory O ℓ (q ∘ p.symm ∘ Sum.inl)
  have distinct (i : I) : read i ≠ mark := by
    intro h
    have eq : (Sum.inr i : Unit ⊕ I) = Sum.inl () := Sum.inr.inj (p.symm.injective h)
    cases eq
  have stable (q : Fin (Nat.card T) → RV0 O) (v : RV0 O) : test (Function.update q mark v) ↔ test q := by
    have e₁ : Function.update q mark v ∘ read = q ∘ read :=
      funext (fun i => Function.update_of_ne (distinct i) _ _)
    have e₂ : Function.update q mark v ∘ p.symm ∘ Sum.inl = q ∘ p.symm ∘ Sum.inl := by
      funext i
      apply Function.update_of_ne
      intro h
      have eq : (Sum.inl i : T) = Sum.inr (.inl ()) := p.symm.injective h
      cases eq
    change (∃ x, (x,Function.update q mark v ∘ read) ∈ D ∧
      P.label x = decodeHistory O ℓ (Function.update q mark v ∘ p.symm ∘ Sum.inl)) ↔ _
    rw [e₁,e₂]
  have left (q : Fin (Nat.card T) → RV0 O) : q ∈ U.setup.second.target.terminalLabels idx ↔
      test q ∧ q mark = t (q ∘ read) := U.labels (q ∘ p.symm)
  have right (q : Fin (Nat.card T) → RV0 O) : q ∈ V.setup.second.target.terminalLabels idy ↔
      test q ∧ q mark = r (q ∘ read) := V.labels (q ∘ p.symm)
  have selected : U.setup.second.target.terminalSelect idx = V.setup.second.target.terminalSelect idy := by
    funext i
    change p.symm (U.pack.symm (U.setup.second.target.select i)) =
      p.symm (V.pack.symm (V.setup.second.target.select i))
    rw [U.select_eq,V.select_eq,U.pack.symm_apply_apply,V.pack.symm_apply_apply]
  exact U.setup.second.target.terminalGradedClass_replace_paradigm V.setup.second.target idx idy mark read
    distinct t r defR test stable left right selected zero hz (fun q _ => sameZero (q ∘ read))

end GeneralizedEuler.Section5
