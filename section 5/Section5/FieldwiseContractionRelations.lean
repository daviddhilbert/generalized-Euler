module

public import Section5.TerminalClassTransport
public import Section5.UnaryFieldwiseContractions

/-! The fieldwise relation compares the actual terminal RV classes
after naming the field tuple. It is stable under a change of carrier
presentation and under equality of the named bases. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z} {M : SortedStructure L E X}

@[expose] def baseRVZero (S : SortedSubstructure M) : S.carrier .rv :=
  ⟨M.funMap .rvZero (fun j => j.elim0),S.closed .rvZero _ (fun j => j.elim0)⟩

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {k n a b : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

variable (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)

@[expose] def terminalCommonBlowup
    (A B : RetainedFieldFamily 𝓜 S 0 k) (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags) : Prop :=
  CommonBlowup (ElementaryClassStep O hO power S neg)
    (A.terminalGradedClass idxA (baseRVZero S) rfl) (B.terminalGradedClass idxB (baseRVZero S) rfl)

@[expose] def fieldwiseCommonBlowup
    (A B : RetainedFieldFamily 𝓜 S n k) (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags) : Prop :=
  ∀ p : fieldAssignment n Z, terminalCommonBlowup ((𝓜).termGenerated (namedTuple S p))
    (((𝓜).termGeneratedAssignment (namedTuple S p) .rv (.inl ⟨_,neg⟩)).property)
    (A.atFieldTuple p) (B.atFieldTuple p) idxA idxB

theorem terminalCommonBlowup_of_carriers
    {A B C D : RetainedFieldFamily 𝓜 S 0 k}
    {idxA : Fin a ≃ A.tags} {idxB : Fin b ≃ B.tags} {idxC : Fin a ≃ C.tags} {idxD : Fin b ≃ D.tags}
    (carA : A.terminalLabels idxA = C.terminalLabels idxC) (selA : A.terminalSelect idxA = C.terminalSelect idxC)
    (carB : B.terminalLabels idxB = D.terminalLabels idxD) (selB : B.terminalSelect idxB = D.terminalSelect idxD)
    (common : terminalCommonBlowup S neg A B idxA idxB) : terminalCommonBlowup S neg C D idxC idxD := by
  have l := A.terminalGradedClass_congr C idxA idxC (baseRVZero S) rfl carA selA
  have r := B.terminalGradedClass_congr D idxB idxD (baseRVZero S) rfl carB selB
  unfold terminalCommonBlowup at common ⊢
  rwa [l,r] at common

theorem terminalCommonBlowup_rebase
    {T : SortedSubstructure 𝓜} (eq : S = T) (negT : rv O (-1) ∈ T.carrier .rv)
    (A B : RetainedFieldFamily 𝓜 S 0 k) (idxA : Fin a ≃ A.tags) (idxB : Fin b ≃ B.tags)
    (common : terminalCommonBlowup S neg A B idxA idxB) :
    terminalCommonBlowup T negT (A.rebaseEq eq) (B.rebaseEq eq) idxA idxB := by
  cases eq
  exact common

end GeneralizedEuler.Section5
