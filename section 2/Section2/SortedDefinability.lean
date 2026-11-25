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

/-- A block of additional RV coordinates. -/
abbrev AddRVCoordinates (Var : TCsort → Type a) (I : Type a) : TCsort → Type a
  | .vf => Var .vf
  | .rv => Var .rv ⊕ I

abbrev AddRVBlock (Var : TCsort → Type a) (n : ℕ) : TCsort → Type a
  | .vf => Var .vf
  | .rv => Var .rv ⊕ Fin n

abbrev appendRVCoordinates (x : ∀ s, Var s → X s) {I : Type a} (y : I → X .rv) :
    ∀ s, AddRVCoordinates Var I s → X s
  | .vf => x .vf
  | .rv => Sum.elim (x .rv) y

abbrev appendRVAssignment (x : ∀ s, Var s → X s) {n : ℕ} (y : Fin n → X .rv) :
    ∀ s, AddRVBlock Var n s → X s
  | .vf => x .vf
  | .rv => Sum.elim (x .rv) y

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

theorem coordinate_eq_term (s : TCsort) (i : Var s)
    (t : SortedTerm L E (fun t => (A t : Type z) ⊕ Var t) s) :
    SortedDefinableOver M A {x | x s i = t.realize M (fun s => Sum.elim Subtype.val (x s))} :=
  ⟨.equal (.var (.inr i)) t, fun _ => Iff.rfl⟩

/-- Fixing the second tuple gives a set definable over the old base and the
coordinates of that tuple. -/
theorem fix_right {W : TCsort → Type b}
    {G : Set (∀ s, (Var s ⊕ W s) → X s)} (hG : SortedDefinableOver M A G)
    (y : ∀ s, W s → X s) :
    SortedDefinableOver M (fun s => A s ∪ Set.range (y s))
      {x | (fun s => Sum.elim (x s) (y s)) ∈ G} := by
  obtain ⟨φ, hφ⟩ := hG
  let rename (s : TCsort) : (A s : Type z) ⊕ (Var s ⊕ W s) →
      ((A s ∪ Set.range (y s) : Set (X s)) : Type z) ⊕ Var s := fun
    | .inl c => .inl ⟨c.val, Or.inl c.property⟩
    | .inr (.inl i) => .inr i
    | .inr (.inr i) => .inl ⟨y s i, Or.inr ⟨i, rfl⟩⟩
  refine ⟨φ.relabel rename, fun x => (hφ _).trans ?_⟩
  rw [φ.realize_relabel]
  have hr : (fun s => Sum.elim Subtype.val (x s) ∘ rename s) =
      (fun s => Sum.elim Subtype.val (Sum.elim (x s) (y s))) := by
    funext s i
    rcases i with c | (i | i) <;> rfl
  rw [hr]

/-- An injective definable graph isolates each input tuple over the old
base and its image tuple. -/
theorem singleton_of_embedding_graph {W : TCsort → Type b}
    (f : D ↪ (∀ s, W s → X s))
    (hf : SortedDefinableOver M A {a : ∀ s, (Var s ⊕ W s) → X s |
      ∃ x : D, x.val = (fun s => a s ∘ Sum.inl) ∧ f x = (fun s => a s ∘ Sum.inr)})
    (x : D) : SortedDefinableOver M (fun s => A s ∪ Set.range (f x s)) {x.val} := by
  have h := hf.fix_right (f x)
  convert h using 1
  ext y
  change y = x.val ↔ ∃ z : D, z.val = y ∧ f z = f x
  exact ⟨fun hy => ⟨x, hy.symm, rfl⟩,
    fun ⟨z, hzy, hzx⟩ => hzy.symm.trans (congrArg Subtype.val (f.injective hzx))⟩

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

/-- Projection of finitely many RV variables keeps the same parameter base. -/
theorem project_rv_block {n : ℕ} {D : Set (∀ s, AddRVBlock Var n s → X s)}
    (hD : SortedDefinableOver M A D) :
    SortedDefinableOver M A {x | ∃ y : Fin n → X .rv, appendRVAssignment x y ∈ D} := by
  induction n with
  | zero =>
    let forget : ∀ s, AddRVBlock Var 0 s → Var s
      | .vf => id
      | .rv => Sum.elim id Fin.elim0
    convert hD.pullback_relabel forget using 1
    ext x
    change (∃ y : Fin 0 → X .rv, appendRVAssignment x y ∈ D) ↔ (fun s => x s ∘ forget s) ∈ D
    have eq (y : Fin 0 → X .rv) : (fun s => x s ∘ forget s) = appendRVAssignment x y := by
      funext s i
      cases s with
      | vf => rfl
      | rv =>
        rcases i with i | i
        · rfl
        · exact i.elim0
    exact ⟨fun ⟨y, hy⟩ => (eq y).symm ▸ hy, fun h => ⟨Fin.elim0, (eq Fin.elim0) ▸ h⟩⟩
  | succ n ih =>
    let rename : ∀ s, AddRVBlock Var (n + 1) s → AddSortedVar (AddRVBlock Var n) .rv s
      | .vf => Sum.inl
      | .rv => Sum.elim (fun i => .inl (.inl i))
          (Fin.lastCases (.inr ⟨rfl⟩) (fun j => .inl (.inr j)))
    have hproj := SortedDefinableOver.project_one .rv (hD.pullback_relabel rename)
    convert ih hproj using 1
    ext x
    have eq (y : Fin n → X .rv) (v : X .rv) :
        (fun s => extendSortedAssignment (appendRVAssignment x y) v s ∘ rename s) =
          appendRVAssignment x (Fin.snoc y v) := by
      funext s i
      cases s with
      | vf => rfl
      | rv =>
        rcases i with i | j
        · rfl
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simp [rename, extendSortedAssignment]
          · simp [rename, extendSortedAssignment]
    change (∃ z : Fin (n + 1) → X .rv, appendRVAssignment x z ∈ D) ↔
      ∃ y : Fin n → X .rv, ∃ v : X .rv,
        (fun s => extendSortedAssignment (appendRVAssignment x y) v s ∘ rename s) ∈ D
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨Fin.init z, z (Fin.last n), ?_⟩
      rwa [eq, Fin.snoc_init_self]
    · rintro ⟨y, v, hy⟩
      exact ⟨Fin.snoc y v, eq y v ▸ hy⟩

theorem project_rv_coordinates {I : Type a} [Finite I]
    {D : Set (∀ s, AddRVCoordinates Var I s → X s)} (hD : SortedDefinableOver M A D) :
    SortedDefinableOver M A {x | ∃ y : I → X .rv, appendRVCoordinates x y ∈ D} := by
  classical
  let := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let rename : ∀ s, AddRVCoordinates Var I s → AddRVBlock Var (Fintype.card I) s
    | .vf => id
    | .rv => Sum.map id e
  have h := SortedDefinableOver.project_rv_block (hD.pullback_relabel rename)
  convert h using 1
  ext x
  change (∃ y : I → X .rv, appendRVCoordinates x y ∈ D) ↔
    ∃ z : Fin (Fintype.card I) → X .rv, (fun s => appendRVAssignment x z s ∘ rename s) ∈ D
  have eq (z : Fin (Fintype.card I) → X .rv) :
      (fun s => appendRVAssignment x z s ∘ rename s) = appendRVCoordinates x (z ∘ e) := by
    funext s i
    cases s with
    | vf => rfl
    | rv => cases i <;> rfl
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ e.symm, ?_⟩
    rw [eq, show (y ∘ e.symm) ∘ e = y from funext fun i => congrArg y (e.symm_apply_apply i)]
    exact hy
  · rintro ⟨z, hz⟩
    exact ⟨z ∘ e, eq z ▸ hz⟩

end SortedDefinableOver

end GeneralizedEuler.Section2
