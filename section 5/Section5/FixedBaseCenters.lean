module

public import Section5.FiniteTests
public import Section2.RecoveredValuedField
import all Section2.GeneratedSubstructure

/-! Fixed-base unary preparation from the immediate-isomorphism criterion. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)

local notation "M" => canonicalStructure (L := L) O hO power

variable (F : FieldTerms (convexLanguage L)) in
def subVF {V : TCsort → Type z} (a b : SortedTerm L E V .vf) : SortedTerm L E V .vf :=
  liftValuedTerm (Fin.cases a (fun _ => b)) F.sub

set_option linter.style.haveILetI false in
theorem eval_subVF (F : FieldTerms (convexLanguage L)) {V : TCsort → Type z}
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (v : ∀ s, V s → CanonicalSort O s) (a b : SortedTerm L E V .vf) :
    (subVF F a b).realize M v = a.realize M v - b.realize M v := by
  letI := convexStructure O L
  have h := realize_liftValuedTerm M (recoveredRing M minusOne) (Fin.cases a (fun _ => b)) F.sub v
  rw [recoveredValuedStructure_canonical_eq O hO power minusOne hm] at h
  rw [subVF, h, hF.sub]
  rfl

theorem eval_rvOfVF {V : TCsort → Type z}
    (v : ∀ s, V s → CanonicalSort O s) (t : SortedTerm L E V .vf) :
    (rvOfVF t).realize M v = rv O (t.realize M v) := by
  rw [← canonicalStructure_rvMap O hO power (L := L), rvOfVF, SortedTerm.realize, SortedStructure.rvMap]
  congr 1
  funext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst i
  rfl

/-- Name the base and leave both candidate VF points and the shared RV
tuple free. Saturation is used for this one tuple of free variables. -/
abbrev CenterTestVariables {X : TCsort → Type z} (B : ∀ s, Set (X s))
    (I : Type) (s : TCsort) : Type z :=
  (B s : Type z) ⊕ MixedVariables 2 I s

abbrev CenterTestAssignments {X : TCsort → Type z} (B : ∀ s, Set (X s)) (I : Type) :
    Set (∀ s, CenterTestVariables B I s → X s) :=
  {v | ∀ s (c : B s), v s (.inl c) = c.val}

variable (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type}

private def unaryAssignment (x : K) (ξ : I → RV0 O) :
    ∀ s, MixedVariables 1 I s → CanonicalSort O s
  | .vf => fun _ => x
  | .rv => ξ

private def candidate (j : Fin 2) :
    ∀ s, (S.carrier s : Type z) ⊕ MixedVariables 1 I s →
      CenterTestVariables S.carrier I s
  | .vf => Sum.map id (fun _ => j)
  | .rv => id

private def pairAssignment (x y : K) (ξ : I → RV0 O) :
    ∀ s, CenterTestVariables S.carrier I s → CanonicalSort O s
  | .vf => Sum.elim Subtype.val (Fin.cases x (fun _ => y))
  | .rv => Sum.elim Subtype.val ξ

private theorem membership_of_immediate_isomorphism
    (A : Set (K × (I → RV0 O)))
    (hA : SortedDefinableOver M S.carrier {a : ∀ s, MixedVariables 1 I s → CanonicalSort O s |
      (a .vf 0, a .rv) ∈ A}) {x y : K} (ξ : I → RV0 O)
    (e : SortedIsomorphism M M) (hxy : e.toEmbedding .vf x = y)
    (hfix : ∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c)
    (hrv : ∀ t, e.toEmbedding .rv t = t) :
    (x, ξ) ∈ A ↔ (y, ξ) ∈ A := by
  obtain ⟨φ, hφ⟩ := hA
  let v (s : TCsort) := Sum.elim (Subtype.val : S.carrier s → CanonicalSort O s) (unaryAssignment (O := O) x ξ s)
  let w (s : TCsort) := Sum.elim (Subtype.val : S.carrier s → CanonicalSort O s) (unaryAssignment (O := O) y ξ s)
  have he : e.toSortedEmbedding.mapAssignment v = w := by
    funext s i
    rw [SortedEmbedding.mapAssignment_apply]
    cases s with
    | vf =>
      rcases i with c | i
      · exact hfix c c.property
      · exact hxy
    | rv =>
      rcases i with c | i
      · exact hrv c
      · exact hrv (ξ i)
  exact (hφ (unaryAssignment O x ξ)).trans
    (((e.realize_iff φ v).symm.trans (he ▸ Iff.rfl)).trans (hφ (unaryAssignment O y ξ)).symm)

set_option linter.style.haveILetI false in
/-- The finite list in Lemma 5.4 is chosen over the original VF sort of
the base and works for the entire RV-parameter family. The immediate
automorphisms are supplied by Section 3's prescribed-point theorem. -/
theorem finite_centers_of_definable
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes M (CenterTestVariables S.carrier I)
      (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism M M, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set (K × (I → RV0 O)))
    (hA : SortedDefinableOver M S.carrier {a : ∀ s, MixedVariables 1 I s → CanonicalSort O s |
      (a .vf 0, a .rv) ∈ A}) :
    ∃ C : Finset (S.carrier .vf), ∀ x y ξ, (∀ c ∈ C, rv O (x - c.val) = rv O (y - c.val)) →
      ((x, ξ) ∈ A ↔ (y, ξ) ∈ A) := by
  classical
  obtain ⟨φ, hφ⟩ := hA
  let V := CenterTestVariables S.carrier I
  let left := φ.relabel (candidate O hO power S 0)
  let right := φ.relabel (candidate O hO power S 1)
  let diff := ((left.imp right).conjunction (right.imp left)).neg
  let translated (j : Fin 2) (c : S.carrier .vf) : SortedTerm L E V .rv :=
    rvOfVF (subVF F (.var (.inr j)) (.var (.inl c)))
  let test (c : S.carrier .vf) := SortedFormula.equal (translated 0 c) (translated 1 c)
  have translated_eq (v : ∀ s, V s → CanonicalSort O s) (j : Fin 2) (c : S.carrier .vf) :
      (translated j c).realize M v = rv O (v .vf (.inr j) - v .vf (.inl c)) := by
    change (rvOfVF (subVF F (.var (.inr j)) (.var (.inl c)))).realize M v = _
    rw [eval_rvOfVF O hO power, eval_subVF O hO power F minusOne hm hF]
    rfl
  have difference_eval (x y : K) (ξ : I → RV0 O) :
      diff.realize M (pairAssignment O hO power S x y ξ) ↔
        ¬ ((x, ξ) ∈ A ↔ (y, ξ) ∈ A) := by
    let v := pairAssignment O hO power S x y ξ
    have eval (j : Fin 2) :
        (φ.relabel (candidate O hO power S j)).realize M v ↔
          ((Fin.cases x (fun _ => y) : Fin 2 → K) j, ξ) ∈ A := by
      rw [φ.realize_relabel]
      let a := unaryAssignment O ((Fin.cases x (fun _ => y) : Fin 2 → K) j) ξ
      have eq : (fun s => v s ∘ candidate O hO power S j s) =
          (fun s => Sum.elim Subtype.val (a s)) := by
        funext s i
        cases s <;> cases i <;> rfl
      rw [eq]
      exact (hφ a).symm
    simp only [diff, SortedFormula.realize_neg, SortedFormula.realize_conjunction,
      SortedFormula.realize, left, right, eval, v, Fin.cases_zero]
    exact not_congr ⟨fun h => Iff.intro h.1 h.2, fun h => ⟨h.mp, h.mpr⟩⟩
  have test_eval (x y : K) (ξ : I → RV0 O) (c : S.carrier .vf) :
      (test c).realize M (pairAssignment O hO power S x y ξ) ↔
        rv O (x - c.val) = rv O (y - c.val) := by
    simp only [test, SortedFormula.realize, translated_eq]
    rfl
  have from_pair (v : ∀ s, V s → CanonicalSort O s)
      (hv : v ∈ CenterTestAssignments S.carrier I) :
      v = pairAssignment O hO power S (v .vf (.inr 0)) (v .vf (.inr 1)) (fun i => v .rv (.inr i)) := by
    funext s i
    cases s with
    | vf =>
      rcases i with c | j
      · exact hv .vf c
      · refine Fin.cases rfl (fun k => ?_) j
        fin_cases k
        rfl
    | rv =>
      rcases i with c | i
      · exact hv .rv c
      · rfl
  obtain ⟨C, hC⟩ := finite_tests M V _ sat diff test (by
    intro v hv htest hdiff
    rw [from_pair v hv] at htest hdiff
    obtain ⟨e, he, hfix, hrv⟩ := immediate _ _ (fun c => (test_eval _ _ _ c).mp (htest c))
    exact (difference_eval _ _ _).mp hdiff
      (membership_of_immediate_isomorphism O hO power S A ⟨φ, hφ⟩ _ e he hfix hrv))
  refine ⟨C, fun x y ξ ht => ?_⟩
  have hc := hC (pairAssignment O hO power S x y ξ) (by intro s c; cases s <;> rfl)
    (fun c hc => (test_eval x y ξ c).mpr (ht c hc))
  exact Classical.byContradiction (fun h => hc ((difference_eval x y ξ).mpr h))

end GeneralizedEuler.Section5
