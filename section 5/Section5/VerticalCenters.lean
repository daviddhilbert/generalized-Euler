module

public import Section5.FixedBaseCenters

/-! Finite uniform center terms in the complementary VF variables.
The disagreement type keeps the entire auxiliary RV tuple free. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

/-- Variables for a single head, a suffix, and an auxiliary RV tuple. -/
abbrev VerticalVariables (n : ℕ) (I : Type) : TCsort → Type
  | .vf => Unit ⊕ Fin n
  | .rv => I

/-- Variables for two heads, a common suffix, and a common RV tuple. -/
abbrev VerticalPairVariables (n : ℕ) (I : Type) : TCsort → Type
  | .vf => Bool ⊕ Fin n
  | .rv => I

abbrev WithBase {X : TCsort → Type z} (B : ∀ s, Set (X s))
    (V : TCsort → Type) (s : TCsort) : Type z :=
  (B s : Type z) ⊕ V s

/-- The base constants are fixed when realizing the disagreement type. -/
abbrev BaseAssignments {X : TCsort → Type z} (B : ∀ s, Set (X s))
    (V : TCsort → Type) : Set (∀ s, WithBase B V s → X s) :=
  {v | ∀ s (c : B s), v s (.inl c) = c.val}

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n : ℕ} {I : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Name the original base and the complementary field tuple. No varying
RV input is needed to evaluate a candidate center. -/
@[expose] def centerAssignment (y : Fin n → K) :
    ∀ s, WithBase S.carrier (MixedVariables n Empty) s → CanonicalSort O s
  | .vf => Sum.elim Subtype.val y
  | .rv => Sum.elim Subtype.val Empty.elim

private def pairAssign (x x' : K) (y : Fin n → K) (ξ : I → RV0 O) :
    ∀ s, WithBase S.carrier (VerticalPairVariables n I) s → CanonicalSort O s
  | .vf => Sum.elim Subtype.val (Sum.elim (fun j => if j then x' else x) y)
  | .rv => Sum.elim Subtype.val ξ

private def oneAssign (x : K) (y : Fin n → K) (ξ : I → RV0 O) :
    ∀ s, VerticalVariables n I s → CanonicalSort O s
  | .vf => Sum.elim (fun _ => x) y
  | .rv => ξ

private def putHead (j : Bool) :
    ∀ s, WithBase S.carrier (VerticalVariables n I) s →
      WithBase S.carrier (VerticalPairVariables n I) s
  | .vf => Sum.map id (Sum.map (fun _ => j) id)
  | .rv => id

private def putCenter :
    ∀ s, WithBase S.carrier (MixedVariables n Empty) s →
      WithBase S.carrier (VerticalPairVariables n I) s
  | .vf => Sum.map id Sum.inr
  | .rv => Sum.map id Empty.elim

set_option linter.style.haveILetI false in
set_option maxHeartbeats 700000 in
/-- Vertically, arbitrary mixed definable membership is decided by
finitely many translated leading terms. The center terms use only the
original base and the complementary field coordinates. -/
theorem finite_vertical_centers
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n I))
      (BaseAssignments S.carrier (VerticalPairVariables n I)))
    (immediate : ∀ (y : Fin n → K) (x x' : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S y)
      (∀ c : B.carrier .vf, rv O (x - c.val) = rv O (x' - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = x' ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set (K × ((Fin n → K) × (I → RV0 O))))
    (hA : SortedDefinableOver 𝓜 S.carrier {a : ∀ s, VerticalVariables n I s → CanonicalSort O s |
      (a .vf (.inl ()), a .vf ∘ Sum.inr, a .rv) ∈ A}) :
    ∃ C : Finset (SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf),
      ∀ (y : Fin n → K) (x x' : K) (ξ : I → RV0 O),
        (∀ t ∈ C, let c := t.realize 𝓜 (centerAssignment O hO power S y)
          rv O (x - c) = rv O (x' - c)) →
        ((x, y, ξ) ∈ A ↔ (x', y, ξ) ∈ A) := by
  classical
  obtain ⟨φ, hφ⟩ := hA
  let V := WithBase S.carrier (VerticalPairVariables n I)
  let W := BaseAssignments S.carrier (VerticalPairVariables n I)
  let left := φ.relabel (putHead O hO power S false)
  let right := φ.relabel (putHead O hO power S true)
  let bad := ((left.imp right).conjunction (right.imp left)).neg
  let translated (j : Bool) (t : SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf) :
      SortedTerm L E V .rv :=
    rvOfVF (subVF F (.var (.inr (.inl j))) (t.relabel (putCenter O hO power S)))
  let test (t : SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf) :=
    SortedFormula.equal (translated false t) (translated true t)
  have eval_test (y : Fin n → K) (x x' : K) (ξ : I → RV0 O)
      (t : SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf) :
      (test t).realize 𝓜 (pairAssign O hO power S x x' y ξ) ↔
        let c := t.realize 𝓜 (centerAssignment O hO power S y)
        rv O (x - c) = rv O (x' - c) := by
    let v := pairAssign O hO power S x x' y ξ
    have he : (fun s => v s ∘ putCenter O hO power S s) = centerAssignment O hO power S y := by
      funext s i
      cases s with
      | vf => cases i <;> rfl
      | rv => rcases i with c | i; exacts [rfl, i.elim]
    simp only [test, translated, SortedFormula.realize, eval_rvOfVF O hO power,
      eval_subVF O hO power F minusOne hm hF, SortedTerm.realize_relabel, SortedTerm.realize]
    dsimp [v] at he
    rw [he]
    rfl
  have eval_bad (y : Fin n → K) (x x' : K) (ξ : I → RV0 O) :
      bad.realize 𝓜 (pairAssign O hO power S x x' y ξ) ↔
        ¬ ((x, y, ξ) ∈ A ↔ (x', y, ξ) ∈ A) := by
    let v := pairAssign O hO power S x x' y ξ
    have hj (j : Bool) :
        (φ.relabel (putHead O hO power S j)).realize 𝓜 v ↔
          ((if j then x' else x), y, ξ) ∈ A := by
      let a := oneAssign O (if j then x' else x) y ξ
      rw [φ.realize_relabel]
      have eq : (fun s => v s ∘ putHead O hO power S j s) =
          (fun s => Sum.elim Subtype.val (a s)) := by
        funext s i
        cases s with
        | vf => rcases i with c | (j | k) <;> rfl
        | rv => cases i <;> rfl
      rw [eq]
      exact (hφ a).symm
    simp only [bad, SortedFormula.realize_neg, SortedFormula.realize_conjunction,
      SortedFormula.realize, left, right, hj, v, Bool.false_eq_true, ↓reduceIte]
    exact not_congr ⟨fun h => Iff.intro h.1 h.2, fun h => ⟨h.mp, h.mpr⟩⟩
  have all_tests (v : ∀ s, V s → CanonicalSort O s) (hw : v ∈ W)
      (ht : ∀ t, (test t).realize 𝓜 v) : ¬ bad.realize 𝓜 v := by
    let x := v .vf (.inr (.inl false))
    let x' := v .vf (.inr (.inl true))
    let y : Fin n → K := fun j => v .vf (.inr (.inr j))
    let ξ : I → RV0 O := fun i => v .rv (.inr i)
    have hv : v = pairAssign O hO power S x x' y ξ := by
      funext s i
      cases s with
      | vf =>
        rcases i with c | (j | k)
        · exact hw .vf c
        · cases j <;> rfl
        · rfl
      | rv =>
        rcases i with c | i
        · exact hw .rv c
        · rfl
    let names := centerAssignment O hO power S y
    let B := SortedStructure.termGenerated 𝓜 names
    have hmatch (c : B.carrier .vf) : rv O (x - c.val) = rv O (x' - c.val) := by
      obtain ⟨t, ht'⟩ := c.property
      rw [← ht']
      exact (eval_test y x x' ξ t).1 (hv ▸ ht t)
    obtain ⟨e, he, hfixed, hrv⟩ := immediate y x x' hmatch
    let a := oneAssign O x y ξ
    let a' := oneAssign O x' y ξ
    let va (s : TCsort) := Sum.elim (Subtype.val : S.carrier s → CanonicalSort O s) (a s)
    let va' (s : TCsort) := Sum.elim (Subtype.val : S.carrier s → CanonicalSort O s) (a' s)
    have ha : e.toSortedEmbedding.mapAssignment va = va' := by
      funext s i
      rw [SortedEmbedding.mapAssignment_apply]
      cases s with
      | vf =>
        rcases i with c | (i | j)
        · exact hfixed c ⟨.var (.inl c), rfl⟩
        · exact he
        · exact hfixed (y j) ⟨.var (.inr j), rfl⟩
      | rv =>
        rcases i with c | i
        · exact hrv c
        · exact hrv (ξ i)
    intro hb
    apply (eval_bad y x x' ξ).1 (hv ▸ hb)
    exact (hφ a).trans (((e.realize_iff φ va).symm.trans (ha ▸ Iff.rfl)).trans (hφ a').symm)
  obtain ⟨C, hC⟩ := finite_tests 𝓜 V W sat bad test all_tests
  refine ⟨C, fun y x x' ξ ht => ?_⟩
  have good : pairAssign O hO power S x x' y ξ ∈ W := by
    intro s c
    cases s <;> rfl
  have hn := hC (pairAssign O hO power S x x' y ξ) good
    (fun t ht' => (eval_test y x x' ξ t).2 (ht t ht'))
  exact Classical.byContradiction (fun h => hn ((eval_bad y x x' ξ).2 h))

end GeneralizedEuler.Section5
