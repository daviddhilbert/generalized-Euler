module

public import Mathlib.ModelTheory.Satisfiability
public import Section2.TaggedSyntax

/-! Compactness for the sorted language of Theorem 2.16. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w b

variable {L : Language.{u, v}} {E : Type w}

private def sortNonemptySentence (s : TCsort) : (taggedLanguage L E).Sentence :=
  Formula.iExs Unit (sortGuardFormula s (.var (.inr ())))

private def functionClosureSentence {ss : List TCsort} {s : TCsort}
    (f : FunctionSymbol L E ss s) : (taggedLanguage L E).Sentence :=
  Formula.iAlls (Fin ss.length)
    ((Formula.iInf fun i => sortGuardFormula (ss.get i) (.var (.inr i))).imp
      (sortGuardFormula s (.func ⟨ss, rfl, s, f⟩ (fun i => .var (.inr i)))))

/-- Sentences needed to extract a sorted model with nonempty sorts. -/
def sortAxioms (L : Language.{u, v}) (E : Type w) : (taggedLanguage L E).Theory :=
  Set.range sortNonemptySentence ∪
    {φ | ∃ (ss : List TCsort) (s : TCsort) (f : FunctionSymbol L E ss s),
      φ = functionClosureSentence f}

private theorem realize_sortNonemptySentence (A : Type b) [(taggedLanguage L E).Structure A]
    (s : TCsort) : A ⊨ sortNonemptySentence (L := L) (E := E) s ↔
      Nonempty (guardedSort (L := L) (E := E) A s) := by
  rw [Sentence.Realize, sortNonemptySentence, Formula.realize_iExs]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨⟨x (), ?_⟩⟩
    rwa [sortGuardFormula, Formula.realize_rel] at hx
  · rintro ⟨⟨x, hx⟩⟩
    refine ⟨fun _ => x, ?_⟩
    rw [sortGuardFormula, Formula.realize_rel]
    exact hx

private theorem realize_functionClosureSentence (A : Type b)
    [(taggedLanguage L E).Structure A] {ss : List TCsort} {s : TCsort}
    (f : FunctionSymbol L E ss s) :
    A ⊨ functionClosureSentence f ↔
      ∀ xs : SortedArgs (guardedSort (L := L) (E := E) A) ss,
        Language.Structure.RelMap (L := taggedLanguage L E) (.sortGuard s)
          (fun _ => Language.Structure.funMap (L := taggedLanguage L E) ⟨ss, rfl, s, f⟩
            (fun i => (xs i).val)) := by
  rw [Sentence.Realize, functionClosureSentence, Formula.realize_iAlls]
  simp only [Formula.realize_imp, Formula.realize_iInf, sortGuardFormula, Formula.realize_rel,
    Term.realize_var, Term.realize_func, Sum.elim_inr]
  constructor
  · intro h xs
    exact h (fun i => (xs i).val) (fun i => (xs i).property)
  · intro h xs hx
    exact h (fun i => ⟨xs i, hx i⟩)

theorem models_sortAxioms_iff (A : Type b) [(taggedLanguage L E).Structure A] :
    A ⊨ sortAxioms L E ↔
      (∀ s, Nonempty (guardedSort (L := L) (E := E) A s)) ∧
        GuardedFunctionsClosed (L := L) (E := E) A := by
  constructor
  · intro h
    exact ⟨fun s => (realize_sortNonemptySentence A s).mp (h.realize_of_mem _
      (Or.inl ⟨s, rfl⟩)), fun {ss s} f =>
        (realize_functionClosureSentence A f).mp (h.realize_of_mem _
          (Or.inr ⟨ss, s, f, rfl⟩))⟩
  · rintro ⟨hne, hcl⟩
    refine ⟨?_⟩
    rintro φ (⟨s, rfl⟩ | ⟨ss, s, f, rfl⟩)
    · exact (realize_sortNonemptySentence A s).mpr (hne s)
    · exact (realize_functionClosureSentence A f).mpr (hcl f)

abbrev SortedSentence (L : Language.{u, v}) (E : Type w) :=
  SortedFormula L E (fun _ => Empty)

abbrev SortedTheory (L : Language.{u, v}) (E : Type w) := Set (SortedSentence L E)

@[expose]
def SortedSentence.realize {X : TCsort → Type b} (M : SortedStructure L E X)
    (φ : SortedSentence L E) : Prop :=
  SortedFormula.realize M φ (fun _ => Empty.elim)

theorem SortedIsomorphism.realize_sentence {X Y : TCsort → Type*}
    {M : SortedStructure L E X} {N : SortedStructure L E Y} (e : SortedIsomorphism M N)
    (φ : SortedSentence L E) : φ.realize M ↔ φ.realize N := by
  have h := e.realize_iff φ (fun _ => Empty.elim)
  have hEmpty : e.toSortedEmbedding.mapAssignment (fun _ => Empty.elim) =
      (fun _ => Empty.elim) := funext fun _ => funext fun x => x.elim
  rw [hEmpty] at h
  exact h.symm

def SortedSentence.toTagged (φ : SortedSentence L E) : (taggedLanguage L E).Sentence :=
  (SortedFormula.toTagged φ).relabel (fun a => a.2)

theorem SortedSentence.realize_toTagged {X : TCsort → Type b} {A : Type*}
    [(taggedLanguage L E).Structure A] {M : SortedStructure L E X}
    (P : GuardedPresentation M A) (φ : SortedSentence L E) :
    A ⊨ φ.toTagged ↔ φ.realize M := by
  rw [Sentence.Realize, SortedSentence.toTagged, Formula.realize_relabel]
  convert SortedFormula.realize_toGuarded P φ (fun _ => Empty.elim) using 2
  · funext a
    exact a.2.elim
  · rfl

@[expose]
def SortedTheory.toTagged (T : SortedTheory L E) : (taggedLanguage L E).Theory :=
  sortAxioms L E ∪ SortedSentence.toTagged '' T

theorem SortedTheory.realize_toTagged_iff {X : TCsort → Type b} {A : Type*}
    [(taggedLanguage L E).Structure A] {M : SortedStructure L E X}
    (P : GuardedPresentation M A) (T : SortedTheory L E) :
    A ⊨ T.toTagged ↔ A ⊨ sortAxioms L E ∧ ∀ φ ∈ T, φ.realize M := by
  simp only [SortedTheory.toTagged, Theory.model_iff]
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (Or.inl hφ),
      fun φ hφ => (φ.realize_toTagged P).mp (h _ (Or.inr ⟨φ, hφ, rfl⟩))⟩
  · rintro ⟨hA, hT⟩ φ (hφ | ⟨ψ, hψ, rfl⟩)
    · exact hA _ hφ
    · exact (ψ.realize_toTagged P).mpr (hT _ hψ)

theorem GuardedPresentation.models_sortAxioms {X : TCsort → Type b} {A : Type*}
    [(taggedLanguage L E).Structure A] {M : SortedStructure L E X}
    (P : GuardedPresentation M A) (d : ∀ s, X s) : A ⊨ sortAxioms L E := by
  apply (models_sortAxioms_iff A).mpr
  constructor
  · exact fun s => ⟨⟨P.sortEmbedding s (d s), (P.guard _ _).mpr ⟨d s, rfl⟩⟩⟩
  · intro ss s f xs
    have lift (i : Fin ss.length) :
        ∃ y : X (ss.get i), P.sortEmbedding _ y = (xs i).val :=
      (P.guard _ _).mp (xs i).property
    choose ys hy using lift
    rw [← funext hy, P.map_fun f ys]
    exact (P.guard _ _).mpr ⟨M.funMap f ys, rfl⟩

/-- Satisfiability in nonempty sorts. The chosen universe accommodates the
model furnished by ordinary first-order compactness. -/
def SortedTheory.IsSatisfiable (T : SortedTheory L E) : Prop :=
  ∃ (X : TCsort → Type (max u v w)) (M : SortedStructure L E X),
    (∀ s, Nonempty (X s)) ∧ ∀ φ ∈ T, φ.realize M

set_option linter.style.haveILetI false in
theorem SortedTheory.isSatisfiable_toTagged_iff (T : SortedTheory L E) :
    T.toTagged.IsSatisfiable ↔ T.IsSatisfiable := by
  constructor
  · intro h
    let A := h.some
    have hA : A ⊨ sortAxioms L E :=
      Theory.Model.mono A.is_model Set.subset_union_left
    obtain ⟨hne, hcl⟩ := (models_sortAxioms_iff A).mp hA
    exact ⟨guardedSort A, extractedStructure A hcl, hne,
      ((T.realize_toTagged_iff (extractedPresentation A hcl)).mp A.is_model).2⟩
  · rintro ⟨X, M, hne, hM⟩
    let d : ∀ s, X s := fun s => Classical.choice (hne s)
    letI := taggedStructure M d
    let P := taggedPresentation M d
    haveI : Nonempty (TaggedCarrier X) := ⟨tag .vf (d .vf)⟩
    haveI : TaggedCarrier X ⊨ T.toTagged :=
      (T.realize_toTagged_iff P).mpr ⟨P.models_sortAxioms d, hM⟩
    exact Theory.Model.isSatisfiable (TaggedCarrier X)

/-- Compactness for theories in the reviewed two-sorted language. -/
theorem SortedTheory.compactness (T : SortedTheory L E)
    (h : ∀ T₀ : Finset (SortedSentence L E), (T₀ : SortedTheory L E) ⊆ T →
      SortedTheory.IsSatisfiable (T₀ : SortedTheory L E)) :
    T.IsSatisfiable := by
  classical
  apply (T.isSatisfiable_toTagged_iff).mp
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro U hU
  let V := U.filter (fun φ => φ ∉ sortAxioms L E)
  have hV : (V : (taggedLanguage L E).Theory) ⊆ SortedSentence.toTagged '' T := by
    intro φ hφ
    obtain ⟨hφU, hφA⟩ := Finset.mem_filter.mp hφ
    exact (hU hφU).resolve_left hφA
  obtain ⟨T₀, hT₀, hVeq⟩ := Finset.subset_set_image_iff.mp hV
  apply ((SortedTheory.isSatisfiable_toTagged_iff (T₀ : SortedTheory L E)).mpr
    (h T₀ hT₀)).mono
  intro φ hφ
  by_cases hφA : φ ∈ sortAxioms L E
  · exact Or.inl hφA
  · have : φ ∈ T₀.image SortedSentence.toTagged :=
      hVeq ▸ Finset.mem_filter.mpr ⟨hφ, hφA⟩
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp this
    exact Or.inr ⟨ψ, hψ, rfl⟩

end GeneralizedEuler.Section2
