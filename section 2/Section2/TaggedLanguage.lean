module

public import Mathlib.ModelTheory.Semantics
public import Section2.SortedStructure

/-! A guarded encoding of the two-sorted signature in Mathlib's
single-sorted first-order language. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

structure TaggedFunction (L : Language.{u, v}) (E : Type w) (n : ℕ) where
  inputs : List TCsort
  arity : inputs.length = n
  output : TCsort
  symbol : FunctionSymbol L E inputs output

inductive TaggedRelation (L : Language.{u, v}) : ℕ → Type v
  | sortGuard (s : TCsort) : TaggedRelation L 1
  | symbol {n : ℕ} (inputs : List TCsort) (arity : inputs.length = n)
      (r : RelationSymbol L inputs) : TaggedRelation L n

abbrev taggedLanguage (L : Language.{u, v}) (E : Type w) : Language :=
  ⟨TaggedFunction L E, TaggedRelation L⟩

abbrev TaggedCarrier (X : TCsort → Type z) := X .vf ⊕ X .rv

def tag {X : TCsort → Type z} : ∀ s, X s → TaggedCarrier X
  | .vf => Sum.inl
  | .rv => Sum.inr

def untag {X : TCsort → Type z} : (s : TCsort) → TaggedCarrier X → Option (X s)
  | .vf, .inl x => some x
  | .vf, .inr _ => none
  | .rv, .inl _ => none
  | .rv, .inr t => some t

@[simp] theorem untag_tag {X : TCsort → Type z} (s : TCsort) (x : X s) :
    untag s (tag s x) = some x := by cases s <;> rfl

theorem tag_injective {X : TCsort → Type z} (s : TCsort) :
    Function.Injective (@tag X s) := by
  cases s
  · exact Sum.inl_injective
  · exact Sum.inr_injective

theorem hasTag_iff {X : TCsort → Type z} (s : TCsort) (x : TaggedCarrier X) :
    (untag s x).isSome ↔ ∃ y : X s, tag s y = x := by
  cases s <;> cases x <;> simp [untag, tag]

private def readTaggedArgs {X : TCsort → Type z} (defaultValue : ∀ s, X s)
    (ss : List TCsort) (xs : Fin ss.length → TaggedCarrier X) : SortedArgs X ss :=
  fun i => (untag (ss.get i) (xs i)).getD (defaultValue (ss.get i))

private abbrev tagsMatch {X : TCsort → Type z} (ss : List TCsort)
    (xs : Fin ss.length → TaggedCarrier X) : Prop :=
  ∀ i, (untag (ss.get i) (xs i)).isSome

/-- The tagged presentation. On the intended sorts it interprets each
symbol as in the original structure. Elsewhere the function values use
the chosen default of the result sort and relations are false. -/
@[instance_reducible]
def taggedStructure {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
    (M : SortedStructure L E X) (defaultValue : ∀ s, X s) :
    (taggedLanguage L E).Structure (TaggedCarrier X) where
  funMap f xs := by
    classical
    let ys := xs ∘ Fin.cast f.arity
    exact tag f.output (if tagsMatch f.inputs ys then
      M.funMap f.symbol (readTaggedArgs defaultValue f.inputs ys) else defaultValue f.output)
  RelMap r xs := match r with
    | .sortGuard s => (untag s (xs 0)).isSome
    | .symbol ss h r =>
      let ys := xs ∘ Fin.cast h
      tagsMatch ss ys ∧ M.relMap r (readTaggedArgs defaultValue ss ys)

theorem tagged_funMap_on_tags {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
    (M : SortedStructure L E X) (defaultValue : ∀ s, X s)
    {ss : List TCsort} {s : TCsort} (f : FunctionSymbol L E ss s) (xs : SortedArgs X ss) :
    @Language.Structure.funMap (taggedLanguage L E) (TaggedCarrier X)
      (taggedStructure M defaultValue) ss.length ⟨ss, rfl, s, f⟩
      (fun i => tag (ss.get i) (xs i)) = tag s (M.funMap f xs) := by
  classical
  change tag s (if tagsMatch ss _ then M.funMap f (readTaggedArgs defaultValue ss _)
    else defaultValue s) = tag s (M.funMap f xs)
  have h : tagsMatch ss (fun i => tag (ss.get i) (xs i)) := by
    intro i
    simp
  have hr : readTaggedArgs defaultValue ss (fun i => tag (ss.get i) (xs i)) = xs := by
    funext i
    simp only [readTaggedArgs, untag_tag, Option.getD_some]
  simp only [Function.comp_def, Fin.cast_refl, id_eq, hr]
  rw [ite_eq_left h]

theorem tagged_relMap_on_tags {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
    (M : SortedStructure L E X) (defaultValue : ∀ s, X s)
    {ss : List TCsort} (r : RelationSymbol L ss) (xs : SortedArgs X ss) :
    @Language.Structure.RelMap (taggedLanguage L E) (TaggedCarrier X)
      (taggedStructure M defaultValue) ss.length (.symbol ss rfl r)
      (fun i => tag (ss.get i) (xs i)) ↔ M.relMap r xs := by
  constructor
  · rintro ⟨_, h⟩
    convert h using 2
    funext i
    simp only [readTaggedArgs, Function.comp_apply, Fin.cast_refl, id_eq, untag_tag, Option.getD_some]
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      simp only [Function.comp_apply, Fin.cast_refl, id_eq, untag_tag, Option.isSome_some]
    · convert h using 2
      funext i
      simp only [readTaggedArgs, Function.comp_apply, Fin.cast_refl, id_eq, untag_tag, Option.getD_some]

theorem tagged_guard_iff {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
    (M : SortedStructure L E X) (defaultValue : ∀ s, X s)
    (s : TCsort) (x : TaggedCarrier X) :
    @Language.Structure.RelMap (taggedLanguage L E) (TaggedCarrier X)
      (taggedStructure M defaultValue) 1 (.sortGuard s) (fun _ => x) ↔
      ∃ y : X s, tag s y = x :=
  hasTag_iff s x

universe b

/-- A sorted structure presented inside a single-sorted structure. The guard
has exactly the range of the embedding for its sort. -/
structure GuardedPresentation {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
    (M : SortedStructure L E X) (A : Type b) [(taggedLanguage L E).Structure A] where
  sortEmbedding : ∀ s, X s ↪ A
  guard : ∀ s x, Language.Structure.RelMap (L := taggedLanguage L E)
    (.sortGuard s) (fun _ => x) ↔ ∃ y, sortEmbedding s y = x
  map_fun : ∀ {ss s} (f : FunctionSymbol L E ss s) (xs : SortedArgs X ss),
    Language.Structure.funMap (L := taggedLanguage L E) ⟨ss, rfl, s, f⟩
      (fun i => sortEmbedding _ (xs i)) = sortEmbedding s (M.funMap f xs)
  map_rel : ∀ {ss} (r : RelationSymbol L ss) (xs : SortedArgs X ss),
    Language.Structure.RelMap (L := taggedLanguage L E) (.symbol ss rfl r)
      (fun i => sortEmbedding _ (xs i)) ↔ M.relMap r xs

/-- The disjoint-sum encoding presents the original sorted structure. -/
def taggedPresentation {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
    (M : SortedStructure L E X) (d : ∀ s, X s) :
    @GuardedPresentation L E X M (TaggedCarrier X) (taggedStructure M d) := by
  letI := taggedStructure M d
  exact { sortEmbedding := fun s => ⟨tag s, tag_injective s⟩
          guard := tagged_guard_iff M d
          map_fun := tagged_funMap_on_tags M d
          map_rel := tagged_relMap_on_tags M d }

section Extraction

variable {L : Language.{u, v}} {E : Type w}
  (A : Type b) [(taggedLanguage L E).Structure A]

/-- The inhabitants of a guarded sort in a single-sorted model. -/
abbrev guardedSort (s : TCsort) :=
  {x : A // Language.Structure.RelMap (L := taggedLanguage L E) (.sortGuard s) (fun _ => x)}

@[expose]
def GuardedFunctionsClosed : Prop :=
  ∀ {ss s} (f : FunctionSymbol L E ss s) (xs : SortedArgs (guardedSort (L := L) (E := E) A) ss),
    Language.Structure.RelMap (L := taggedLanguage L E) (.sortGuard s)
      (fun _ => Language.Structure.funMap (L := taggedLanguage L E) ⟨ss, rfl, s, f⟩
        (fun i => (xs i).val))

def extractedStructure (h : GuardedFunctionsClosed (L := L) (E := E) A) :
    SortedStructure L E (guardedSort (L := L) (E := E) A) where
  funMap f xs := ⟨Language.Structure.funMap (L := taggedLanguage L E) ⟨_, rfl, _, f⟩
    (fun i => (xs i).val), h f xs⟩
  relMap r xs := Language.Structure.RelMap (L := taggedLanguage L E) (.symbol _ rfl r)
    (fun i => (xs i).val)

/-- Closure under the operations suffices to extract the sorted structure.
Quantifiers in the translated syntax already restrict to the right guard. -/
def extractedPresentation (h : GuardedFunctionsClosed (L := L) (E := E) A) :
    GuardedPresentation (extractedStructure A h) A where
  sortEmbedding _ := Function.Embedding.subtype _
  guard _ x := ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨⟨_, hy⟩, hxy⟩ => hxy ▸ hy⟩
  map_fun _ _ := rfl
  map_rel _ _ := Iff.rfl

end Extraction

end GeneralizedEuler.Section2
