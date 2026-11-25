module

public import Section2.TaggedTheory

/-! Compactness for partial types in the sorted language. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w a b

variable {L : Language.{u, v}} {E : Type w} {Var : TCsort → Type a}

private abbrev parameterLanguage (L : Language.{u, v}) (E : Type w) (Var : TCsort → Type a) :=
  (taggedLanguage L E)[[TaggedVar Var]]

private def formulaAsSentence (φ : SortedFormula L E Var) :
    (parameterLanguage L E Var).Sentence :=
  Formula.equivSentence φ.toTagged

private def parameterAxioms (T : SortedTheory L E) (Var : TCsort → Type a) :
    (parameterLanguage L E Var).Theory :=
  ((taggedLanguage L E).lhomWithConstants (TaggedVar Var)).onTheory T.toTagged ∪
    Set.range (fun x : TaggedVar Var => Formula.equivSentence (sortGuardFormula x.1 (.var x)))

private def parameterTheory (T : SortedTheory L E) (Δ : Set (SortedFormula L E Var)) :
    (parameterLanguage L E Var).Theory :=
  parameterAxioms T Var ∪ formulaAsSentence '' Δ

/-- A simultaneous realization of a family of formulas in a model of the
sorted theory. -/
@[expose]
def SortedTheory.Realizable (T : SortedTheory L E) (Δ : Set (SortedFormula L E Var)) : Prop :=
  ∃ (X : TCsort → Type (max u v w a)) (M : SortedStructure L E X) (x : ∀ s, Var s → X s),
    (∀ s, Nonempty (X s)) ∧ (∀ φ ∈ T, φ.realize M) ∧ ∀ φ ∈ Δ, φ.realize M x

private theorem parameterTheory_isSatisfiable_iff (T : SortedTheory L E)
    (Δ : Set (SortedFormula L E Var)) :
    (parameterTheory T Δ).IsSatisfiable ↔ T.Realizable Δ := by
  constructor
  · intro h
    let A := h.some
    let L₁ := taggedLanguage L E
    let l := L₁.lhomWithConstants (TaggedVar Var)
    let := l.reduct A
    have hT : A ⊨ T.toTagged := (LHom.onTheory_model l _).mp
      (Theory.Model.mono A.is_model (Set.subset_union_left.trans Set.subset_union_left))
    have hA : A ⊨ sortAxioms L E := Theory.Model.mono hT Set.subset_union_left
    obtain ⟨hne, hcl⟩ := (models_sortAxioms_iff A).mp hA
    let M := extractedStructure A hcl
    let P := extractedPresentation A hcl
    let value (x : TaggedVar Var) : A := L₁.con x
    have hvalue (x : TaggedVar Var) :
        (sortGuardFormula (L := L) (E := E) x.1 (.var x)).Realize value :=
      (Formula.realize_equivSentence A _).mp
        (A.is_model.realize_of_mem _ (Or.inl (Or.inr ⟨x, rfl⟩)))
    have lift (x : TaggedVar Var) : ∃ y, P.sortEmbedding x.1 y = value x :=
      (sortGuardFormula_realize P value x.1 (.var x)).mp (hvalue x)
    choose y hy using lift
    let assign (s : TCsort) (x : Var s) : guardedSort A s := y ⟨s, x⟩
    have hass : P.assignment assign = value := funext fun x => hy x
    refine ⟨guardedSort A, M, assign, hne, ((T.realize_toTagged_iff P).mp hT).2, ?_⟩
    intro φ hφ
    apply (φ.realize_toGuarded P assign).mp
    rw [hass]
    exact (Formula.realize_equivSentence A _).mp
      (A.is_model.realize_of_mem _ (Or.inr ⟨φ, hφ, rfl⟩))
  · rintro ⟨X, M, x, hne, hT, hΔ⟩
    let d : ∀ s, X s := fun s => Classical.choice (hne s)
    let := taggedStructure M d
    let P := taggedPresentation M d
    let L₁ := taggedLanguage L E
    let : (constantsOn (TaggedVar Var)).Structure (TaggedCarrier X) :=
      constantsOn.structure (P.assignment x)
    have : Nonempty (TaggedCarrier X) := ⟨tag .vf (d .vf)⟩
    have hA : TaggedCarrier X ⊨ T.toTagged :=
      (T.realize_toTagged_iff P).mpr ⟨P.models_sortAxioms d, hT⟩
    have : TaggedCarrier X ⊨ parameterTheory T Δ := by
      refine ⟨?_⟩
      rintro σ ((hσ | ⟨y, rfl⟩) | ⟨φ, hφ, rfl⟩)
      · have hExp := (LHom.onTheory_model (L₁.lhomWithConstants (TaggedVar Var)) _).mpr hA
        exact hExp.realize_of_mem _ hσ
      · apply (Formula.realize_equivSentence (TaggedCarrier X) _).mpr
        exact (sortGuardFormula_realize P (P.assignment x) y.1 (.var y)).mpr ⟨x y.1 y.2, rfl⟩
      · exact (Formula.realize_equivSentence (TaggedCarrier X) φ.toTagged).mpr
          ((φ.realize_toGuarded P x).mpr (hΔ φ hφ))
    exact Theory.Model.isSatisfiable (TaggedCarrier X)

theorem SortedTheory.realizable_of_finite (T : SortedTheory L E)
    (Δ : Set (SortedFormula L E Var))
    (hfin : ∀ U : Finset (SortedFormula L E Var), (U : Set (SortedFormula L E Var)) ⊆ Δ →
      T.Realizable (U : Set (SortedFormula L E Var))) : T.Realizable Δ := by
  classical
  apply (parameterTheory_isSatisfiable_iff T Δ).mp
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro U hU
  let V := U.filter (fun φ => φ ∉ parameterAxioms T Var)
  have hV : (V : Set _) ⊆ formulaAsSentence '' Δ := by
    intro φ hφ
    obtain ⟨hφU, hφA⟩ := Finset.mem_filter.mp hφ
    exact (hU hφU).resolve_left hφA
  obtain ⟨Δ₀, hΔ₀, heq⟩ := Finset.subset_set_image_iff.mp hV
  apply ((parameterTheory_isSatisfiable_iff T _).mpr (hfin Δ₀ hΔ₀)).mono
  intro φ hφ
  by_cases hφA : φ ∈ parameterAxioms T Var
  · exact Or.inl hφA
  · have hi : φ ∈ Δ₀.image formulaAsSentence := heq ▸ Finset.mem_filter.mpr ⟨hφ, hφA⟩
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hi
    exact Or.inr ⟨ψ, hψ, rfl⟩

end GeneralizedEuler.Section2
