module

public import Section2.SortedSyntax

/-! Parameters, substructures and the back-and-forth criterion for the
reviewed two-sorted language. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z z' a

variable {L : Language.{u, v}} {E : Type w}
  {X : TCsort → Type z} {Y : TCsort → Type z'}
  (M : SortedStructure L E X) (N : SortedStructure L E Y)

/-- Definability over the two sets of named parameters. Convention 2.1
allows the full carrier of each sort as its parameter set. -/
def SortedDefinableOver {Var : TCsort → Type a}
    (A : ∀ s, Set (X s)) (D : Set (∀ s, Var s → X s)) : Prop :=
  ∃ φ : SortedFormula L E (fun s => (A s : Type z) ⊕ Var s),
    ∀ x, x ∈ D ↔ φ.realize M (fun s => Sum.elim Subtype.val (x s))

/-- A two-sorted substructure is closed under every named operation. -/
structure SortedSubstructure where
  carrier : ∀ s, Set (X s)
  closed : ∀ {ss s} (f : FunctionSymbol L E ss s) (xs : SortedArgs X ss),
    (∀ i, xs i ∈ carrier (ss.get i)) → M.funMap f xs ∈ carrier s

namespace SortedSubstructure

variable {M}

@[expose]
def structureOn (A : SortedSubstructure M) :
    SortedStructure L E (fun s => A.carrier s) where
  funMap f xs := ⟨M.funMap f (fun i => xs i), A.closed f _ (fun i => (xs i).property)⟩
  relMap r xs := M.relMap r (fun i => xs i)

def inclusion (A : SortedSubstructure M) : SortedEmbedding A.structureOn M where
  toEmbedding s := Function.Embedding.subtype (· ∈ A.carrier s)
  map_fun _ _ := rfl
  map_rel _ _ := Iff.rfl

end SortedSubstructure

/-- A system of matching assignments with the two one-element extension
properties. Quantifiers extend the assignment in their own sort. -/
structure SortedBackAndForth where
  related : ∀ (Var : TCsort → Type a),
    (∀ s, Var s → X s) → (∀ s, Var s → Y s) → Prop
  qf : ∀ {Var} {vX : ∀ s, Var s → X s} {vY : ∀ s, Var s → Y s},
    related Var vX vY → ∀ φ : SortedFormula L E Var, φ.IsQF →
      (φ.realize M vX ↔ φ.realize N vY)
  forth : ∀ {Var} {vX : ∀ s, Var s → X s} {vY : ∀ s, Var s → Y s},
    related Var vX vY → ∀ (s : TCsort) (x : X s),
      ∃ y : Y s, related (AddSortedVar Var s) (extendSortedAssignment vX x)
        (extendSortedAssignment vY y)
  back : ∀ {Var} {vX : ∀ s, Var s → X s} {vY : ∀ s, Var s → Y s},
    related Var vX vY → ∀ (s : TCsort) (y : Y s),
      ∃ x : X s, related (AddSortedVar Var s) (extendSortedAssignment vX x)
        (extendSortedAssignment vY y)

theorem SortedBackAndForth.realize_iff (B : SortedBackAndForth.{u, v, w, z, z', a} M N)
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∀ {vX : ∀ s, Var s → X s} {vY : ∀ s, Var s → Y s}, B.related Var vX vY →
      (φ.realize M vX ↔ φ.realize N vY) := by
  induction φ with
  | falsum => intros; rfl
  | equal x y => intro _ _ h; exact B.qf h _ (.equal x y)
  | rel r ts => intro _ _ h; exact B.qf h _ (.rel r ts)
  | imp φ ψ ihφ ihψ =>
    intro _ _ h
    simp only [SortedFormula.realize, ihφ h, ihψ h]
  | all s φ ih =>
    intro vX vY h
    simp only [SortedFormula.realize]
    constructor
    · intro hX y
      obtain ⟨x, hxy⟩ := B.back h s y
      exact (ih hxy).mp (hX x)
    · intro hY x
      obtain ⟨y, hxy⟩ := B.forth h s x
      exact (ih hxy).mpr (hY y)

end GeneralizedEuler.Section2
