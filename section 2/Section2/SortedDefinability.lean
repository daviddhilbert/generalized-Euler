module

public import Section2.SortedModelTheory
public import Section2.SortedQE

/-! Operations on definable sets that retain their fixed parameter base. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z a b

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {M : SortedStructure L E X} {Var : TCsort → Type a} {A B : ∀ s, Set (X s)}
  {D F : Set (∀ s, Var s → X s)}

namespace SortedDefinableOver

theorem mono (hD : SortedDefinableOver M A D) (hAB : ∀ s, A s ⊆ B s) :
    SortedDefinableOver M B D := by
  obtain ⟨φ, hφ⟩ := hD
  let rename (s : TCsort) : (A s : Type z) ⊕ Var s → (B s : Type z) ⊕ Var s :=
    Sum.map (fun x => ⟨x.val, hAB s x.property⟩) id
  refine ⟨φ.relabel rename, fun x => (hφ x).trans ?_⟩
  rw [φ.realize_relabel]
  have h : (fun s => Sum.elim Subtype.val (x s) ∘ rename s) =
      (fun s => Sum.elim Subtype.val (x s)) := by
    funext s t
    cases t <;> rfl
  rw [h]

theorem compl (hD : SortedDefinableOver M A D) : SortedDefinableOver M A Dᶜ := by
  obtain ⟨φ, hφ⟩ := hD
  exact ⟨φ.neg, fun x => (not_congr (hφ x)).trans (φ.realize_neg M _).symm⟩

theorem inter (hD : SortedDefinableOver M A D) (hF : SortedDefinableOver M A F) :
    SortedDefinableOver M A (D ∩ F) := by
  obtain ⟨φ, hφ⟩ := hD
  obtain ⟨ψ, hψ⟩ := hF
  exact ⟨φ.conjunction ψ, fun x =>
    ((hφ x).and (hψ x)).trans (SortedFormula.realize_conjunction M _ φ ψ).symm⟩

theorem union (hD : SortedDefinableOver M A D) (hF : SortedDefinableOver M A F) :
    SortedDefinableOver M A (D ∪ F) := by
  obtain ⟨φ, hφ⟩ := hD
  obtain ⟨ψ, hψ⟩ := hF
  exact ⟨φ.disjunction ψ, fun x =>
    ((hφ x).or (hψ x)).trans (SortedFormula.realize_disjunction M _ φ ψ).symm⟩

/-- Finite unions preserve the same named parameter sets. -/
theorem iUnion {I : Type*} [Finite I] {B : I → Set (∀ s, Var s → X s)}
    (hB : ∀ i, SortedDefinableOver M A (B i)) : SortedDefinableOver M A (⋃ i, B i) := by
  classical
  let := Fintype.ofFinite I
  choose φ hφ using hB
  refine ⟨SortedFormula.anyOf (Finset.univ.toList.map φ), fun x => ?_⟩
  simp only [Set.mem_iUnion, SortedFormula.realize_anyOf, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨φ i, ⟨i, rfl⟩, (hφ i x).mp hi⟩
  · rintro ⟨_, ⟨i, rfl⟩, hi⟩
    exact ⟨i, (hφ i x).mpr hi⟩

theorem iInter {I : Type*} [Finite I] {B : I → Set (∀ s, Var s → X s)}
    (hB : ∀ i, SortedDefinableOver M A (B i)) : SortedDefinableOver M A (⋂ i, B i) := by
  classical
  have h := (iUnion (fun i => (hB i).compl)).compl
  simpa only [Set.compl_iUnion, compl_compl] using h

/-- Renaming or repeating coordinates of a definable set keeps the same
parameters. -/
theorem pullback_relabel (hD : SortedDefinableOver M A D) {W : TCsort → Type b}
    (f : ∀ s, Var s → W s) :
    SortedDefinableOver M A {x | (fun s => x s ∘ f s) ∈ D} := by
  obtain ⟨φ, hφ⟩ := hD
  let rename (s : TCsort) : (A s : Type z) ⊕ Var s → (A s : Type z) ⊕ W s :=
    Sum.map id (f s)
  refine ⟨φ.relabel rename, fun x => (hφ _).trans ?_⟩
  rw [φ.realize_relabel]
  have hr : (fun s => Sum.elim Subtype.val (x s) ∘ rename s) =
      (fun s => Sum.elim Subtype.val (x s ∘ f s)) := by
    funext s i
    cases i <;> rfl
  rw [hr]

theorem coordinate_eq (s : TCsort) (i j : Var s) :
    SortedDefinableOver M A {x | x s i = x s j} :=
  ⟨.equal (.var (.inr i)) (.var (.inr j)), fun _ => Iff.rfl⟩

theorem coordinate_eq_parameter (s : TCsort) (i : Var s) (c : A s) :
    SortedDefinableOver M A {x | x s i = c.val} :=
  ⟨.equal (.var (.inr i)) (.var (.inl c)), fun _ => Iff.rfl⟩

/-- Existential projection of one variable keeps the same parameter sets. -/
theorem project_one (s : TCsort) {D : Set (∀ t, AddSortedVar Var s t → X t)}
    (hD : SortedDefinableOver M A D) :
    SortedDefinableOver M A
      {x : ∀ t, Var t → X t | ∃ y : X s, extendSortedAssignment x y ∈ D} := by
  classical
  obtain ⟨φ, hφ⟩ := hD
  let rename (t : TCsort) :
      (A t : Type z) ⊕ AddSortedVar Var s t →
        AddSortedVar (fun t => (A t : Type z) ⊕ Var t) s t := fun
    | .inl a => .inl (.inl a)
    | .inr (.inl x) => .inl (.inr x)
    | .inr (.inr h) => .inr h
  let ψ := φ.relabel rename
  refine ⟨(.all s ψ.neg : SortedFormula L E (fun t => (A t : Type z) ⊕ Var t)).neg, ?_⟩
  intro x
  let v (t : TCsort) : (A t : Type z) ⊕ Var t → X t := Sum.elim Subtype.val (x t)
  have hψ (y : X s) :
      ψ.realize M (extendSortedAssignment v y) ↔ extendSortedAssignment x y ∈ D := by
    change (φ.relabel rename).realize M _ ↔ _
    rw [φ.realize_relabel]
    have h : (fun t => extendSortedAssignment v y t ∘ rename t) =
        (fun t => Sum.elim Subtype.val (extendSortedAssignment x y t)) := by
      funext t w
      rcases w with a | (b | h)
      · rfl
      · rfl
      · rfl
    rw [h]
    exact (hφ _).symm
  change (∃ y : X s, extendSortedAssignment x y ∈ D) ↔
    ((.all s ψ.neg : SortedFormula L E (fun t => (A t : Type z) ⊕ Var t)).neg).realize M v
  simp only [SortedFormula.realize_neg, SortedFormula.realize, hψ, not_forall, not_not]

end SortedDefinableOver

end GeneralizedEuler.Section2
