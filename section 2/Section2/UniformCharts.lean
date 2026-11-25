module

public import Section2.DefinableCharts
public import Section2.SortedQuantifierBlock

/-! From pointwise coordinate isolation to uniform charts in Lemma 2.26. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z a

abbrev NamedChartVariables (Param : TCsort → Type a) (n : ℕ) (R : Type) (s : TCsort) :=
  Param s ⊕ MixedVariables n R s

@[expose]
def replaceChartField {Param : TCsort → Type a} {X : TCsort → Type z} {n : ℕ} {R : Type}
    (v : ∀ s, NamedChartVariables Param n R s → X s) (x : Fin n → X .vf) :
    ∀ s, NamedChartVariables Param n R s → X s
  | .vf, .inr i => x i
  | .vf, .inl c => v .vf (.inl c)
  | .rv, i => v .rv i

variable {L : Language.{u, v}} {E : Type w}
  {Param : TCsort → Type a} {n k : ℕ} {R : Type}

private def chartReplacement (s : TCsort) :
    NamedChartVariables Param n R s → AddSortedBlock (NamedChartVariables Param n R) .vf n s
  | .inl c => .inl (.inl c)
  | .inr i => match s with
    | .vf => .inr ⟨i, ⟨rfl⟩⟩
    | .rv => .inl (.inr i)

private def chartCoordinateEqualities {m : ℕ} (p : Fin m → Fin n) :
    SortedFormula L E (AddSortedBlock (NamedChartVariables Param n R) .vf n) :=
  SortedFormula.allOf (List.ofFn fun i =>
    .equal (.var (s := .vf) (.inl (.inr (p i)))) (.var (.inr ⟨p i, ⟨rfl⟩⟩)))

/-- A chart code specifies the retained coordinates and a formula
that isolates the remaining coordinates when the retained ones are fixed. -/
structure ProjectionChart (L : Language.{u, v}) (E : Type w)
    (Param : TCsort → Type a) (n : ℕ) (R : Type) (k : ℕ) where
  size : ℕ
  size_le : size ≤ k
  coordinates : Fin size ↪ Fin n
  formula : SortedFormula L E (NamedChartVariables Param n R)

namespace ProjectionChart

variable (C : ProjectionChart L E Param n R k)

/-- The guard keeps the points of the chart formula that are uniquely
determined by their chosen coordinates and all their RV coordinates. -/
def guard : SortedFormula L E (NamedChartVariables Param n R) :=
  let same := chartCoordinateEqualities (Param := Param) (R := R) C.coordinates.toFun
  let all := chartCoordinateEqualities (Param := Param) (R := R) (id : Fin n → Fin n)
  C.formula.conjunction (.allBlock .vf n
    (.imp (same.conjunction (C.formula.relabel chartReplacement)) all))

theorem realize_guard {X : TCsort → Type z} (M : SortedStructure L E X)
    (v : ∀ s, NamedChartVariables Param n R s → X s) :
    C.guard.realize M v ↔ C.formula.realize M v ∧
      ∀ x : Fin n → X .vf, (∀ i, v .vf (.inr (C.coordinates i)) = x (C.coordinates i)) →
        C.formula.realize M (replaceChartField v x) → ∀ i, v .vf (.inr i) = x i := by
  have eq (x : Fin n → X .vf) :
      (fun s => appendSortedBlock v x s ∘ chartReplacement s) = replaceChartField v x := by
    funext s i
    cases s <;> cases i <;> rfl
  have coords {m : ℕ} (p : Fin m → Fin n) (x : Fin n → X .vf) :
      (chartCoordinateEqualities (Param := Param) (R := R) (L := L) (E := E) p).realize M
        (appendSortedBlock v x) ↔ ∀ i, v .vf (.inr (p i)) = x (p i) := by
    simp only [chartCoordinateEqualities, SortedFormula.realize_allOf, List.mem_ofFn,
      forall_exists_index, forall_apply_eq_imp_iff, SortedFormula.realize, SortedTerm.realize,
      appendSortedBlock]
  simp only [guard, SortedFormula.realize_conjunction, SortedFormula.realize_allBlock,
    SortedFormula.realize, SortedFormula.realize_conjunction, coords,
    SortedFormula.realize_relabel, eq, and_imp, id_eq, Function.Embedding.toFun_eq_coe]

end ProjectionChart

set_option linter.style.haveILetI false in
/-- Compactness makes local coordinate isolation uniform, and the
guarded pieces give the definable injection over the original base. -/
theorem exists_definable_embedding_of_local_projection_charts
    {X : TCsort → Type (max u v w z)} (T : SortedTheory L E) (M : SortedStructure L E X)
    (hM : ∀ ψ ∈ T, ψ.realize M) (hX : ∀ s, Nonempty (X s))
    (A : ∀ s, Set (X s)) [Finite R]
    (D : Set (MixedTuple X n R))
    (φ : SortedFormula L E (NamedChartVariables (fun s => (A s : Type (max u v w z))) n R))
    (hD : ∀ x : (∀ s, MixedVariables n R s → X s),
      mixedTuple x ∈ D ↔ φ.realize M (fun s => Sum.elim Subtype.val (x s)))
    (hlocal : ∀ P : T.PointedModel (NamedChartVariables (fun s => (A s : Type (max u v w z))) n R),
      P.realizes φ → ∃ C : ProjectionChart L E (fun s => (A s : Type (max u v w z))) n R k,
        C.formula.realize P.model P.point ∧
        ∀ x : Fin n → P.carrier .vf, (∀ i, P.point .vf (.inr (C.coordinates i)) = x (C.coordinates i)) →
          C.formula.realize P.model (replaceChartField P.point x) →
            ∀ i, P.point .vf (.inr i) = x i)
    (padding : A .vf) (tag : ℕ ↪ X .rv) (htag : ∀ i, tag i ∈ A .rv) :
    ∃ f : D ↪ (Fin k → X .vf) × ((R → X .rv) × X .rv),
      SortedDefinableOver M A {a : ∀ s, ChartGraphVariables n R k s → X s |
        ∃ x : D, x.val = chartInput a ∧ f x = chartOutput a} := by
  classical
  let Code := ProjectionChart L E (fun s => (A s : Type (max u v w z))) n R k
  obtain ⟨U, hU⟩ := T.exists_finite_formula_cover φ (fun C : Code => C.guard) (by
    intro P hp
    obtain ⟨C, hC⟩ := hlocal P hp
    exact ⟨C, (C.realize_guard P.model P.point).mpr hC⟩)
  let enum := Fintype.equivFin {c : Code // c ∈ U}
  let code (i : Fin (Fintype.card {c : Code // c ∈ U})) := (enum.symm i).val
  let tupleAssignment (x : MixedTuple X n R) : ∀ s, MixedVariables n R s → X s
    | .vf => x.1
    | .rv => x.2
  let assignment (x : MixedTuple X n R) (s : TCsort) :
      NamedChartVariables (fun s => (A s : Type (max u v w z))) n R s → X s :=
    Sum.elim Subtype.val (tupleAssignment x s)
  have tupleEta (x : MixedTuple X n R) : mixedTuple (tupleAssignment x) = x := rfl
  let pieces (i : Fin (Fintype.card {c : Code // c ∈ U})) : Set (MixedTuple X n R) :=
    {x | (code i).guard.realize M (assignment x)}
  refine exists_definable_embedding_of_projection_cover D pieces ⟨φ, hD⟩ ?_ ?_
    (fun i => (code i).size) (fun i => (code i).size_le) (fun i => (code i).coordinates)
    ?_ padding (Fin.valEmbedding.trans tag) (fun i => htag i.val)
  · intro i
    refine ⟨(code i).guard, fun x => ?_⟩
    have eq : tupleAssignment (mixedTuple x) = x := by funext s; cases s <;> rfl
    change (code i).guard.realize M (assignment (mixedTuple x)) ↔ _
    simp only [assignment, eq]
  · intro x hx
    let P : T.PointedModel (NamedChartVariables (fun s => (A s : Type (max u v w z))) n R) :=
      ⟨X, M, assignment x, hX, hM⟩
    have hp : P.realizes φ := (hD (tupleAssignment x)).mp (tupleEta x ▸ hx)
    obtain ⟨C, hC, hreal⟩ := hU P hp
    refine ⟨enum ⟨C, hC⟩, ?_⟩
    change (code (enum ⟨C, hC⟩)).guard.realize M (assignment x)
    simpa only [SortedTheory.PointedModel.realizes, P, code, Equiv.symm_apply_apply] using hreal
  · intro i x hx y hy hxy
    have hxg := ((code i).realize_guard M (assignment x)).mp hx.2
    have hyg := ((code i).realize_guard M (assignment y)).mp hy.2
    have hrv : x.2 = y.2 :=
      congrArg (fun p : (Fin (code i).size → X .vf) × (R → X .rv) => p.2) hxy
    have rep : replaceChartField (assignment x) y.1 = assignment y := by
      funext s j
      cases s <;> cases j <;> simp [replaceChartField, assignment, tupleAssignment, hrv]
    have hp (j) : x.1 ((code i).coordinates j) = y.1 ((code i).coordinates j) :=
      congrFun (congrArg Prod.fst hxy) j
    have hfield := hxg.2 y.1 hp (rep.symm ▸ hyg.1)
    exact Prod.ext (funext hfield) hrv

end GeneralizedEuler.Section2
