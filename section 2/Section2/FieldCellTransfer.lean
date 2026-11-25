module

public import Section2.FieldReduct
public import Section2.FieldOperations

/-! Unary cell decompositions over an elementary submodel transfer to
both ambient fields in a prescribed adjunction. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v z

variable {L : Language.{u, v}} (F : OrderedFieldTerms L)

private def strictOrder {V : Type*} (a b : L.Term V) : L.Formula V :=
  (F.le.formula ![b, a]).not

private theorem realize_strictOrder {V K : Type*} [Field K] [LinearOrder K] [L.Structure K]
    (hF : InterpretsOrderedFieldTerms (A := K) F) (a b : L.Term V) (v : V → K) :
    (strictOrder F a b).Realize v ↔ a.realize v < b.realize v := by
  simp only [strictOrder, Formula.realize_not, Formula.realize_rel, hF.le,
    Matrix.cons_val_zero, Matrix.cons_val_one, not_le]

private def unaryCellFormula {A : Type*} (c : UnaryCellCode A) : L.Formula (A ⊕ Unit) :=
  let x : L.Term (A ⊕ Unit) := .var (.inr ())
  let t (a : A) : L.Term (A ⊕ Unit) := .var (.inl a)
  match c with
  | .univ => ⊤
  | .point a => x.equal (t a)
  | .below a => strictOrder F x (t a)
  | .above a => strictOrder F (t a) x
  | .between a b => strictOrder F (t a) x ⊓ strictOrder F x (t b)

private theorem realize_unaryCellFormula {A K : Type*} [Field K] [LinearOrder K] [L.Structure K]
    (hF : InterpretsOrderedFieldTerms (A := K) F) (c : UnaryCellCode A) (p : A → K) (x : K) :
    (unaryCellFormula F c).Realize (Sum.elim p (fun _ => x)) ↔ x ∈ c.asSet p := by
  cases c <;> simp only [unaryCellFormula, UnaryCellCode.asSet, Formula.realize_top, Formula.realize_equal,
    realize_strictOrder F hF, Formula.realize_inf, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    Set.mem_univ, Set.mem_singleton_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]

private theorem exists_cell_code {A : Type*} [Field A] [LinearOrder A]
    {s : Set A} (h : IsUnaryCell s) : ∃ c : UnaryCellCode A, c.asSet id = s := by
  rcases h with h | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, b, h⟩
  · exact ⟨.univ, h.symm⟩
  · exact ⟨.point a, h.symm⟩
  · exact ⟨.below a, h.symm⟩
  · exact ⟨.above a, h.symm⟩
  · exact ⟨.between a b, h.symm⟩

/-- The decomposition of a unary formula over the old field is
expressible as a single universal formula over the same base. It
therefore applies in each elementary extension with the same cells. -/
theorem exists_common_unary_cells
    {A K N : Type z} [Field A] [LinearOrder A] [IsStrictOrderedRing A] [L.Structure A]
    [Field K] [LinearOrder K] [L.Structure K] [Field N] [LinearOrder N] [L.Structure N]
    (hA : InterpretsOrderedFieldTerms (A := A) F)
    (hK : InterpretsOrderedFieldTerms (A := K) F) (hN : InterpretsOrderedFieldTerms (A := N) F)
    (hOM : IsOMinimal (K := A) L) (p : A ↪ₑ[L] K) (q : A ↪ₑ[L] N)
    (φ : L.Formula (A ⊕ Unit)) :
    ∃ (n : ℕ) (cells : Fin n → UnaryCellCode A),
      (∀ x : K, φ.Realize (Sum.elim p (fun _ => x)) ↔ x ∈ ⋃ i, (cells i).asSet p) ∧
      (∀ y : N, φ.Realize (Sum.elim q (fun _ => y)) ↔ y ∈ ⋃ i, (cells i).asSet q) := by
  classical
  let S : Set A := {x | φ.Realize (Sum.elim id (fun _ => x))}
  have hdef : (Set.univ : Set A).Definable₁ L S := by
    apply Set.definable_iff_exists_formula_sum.mpr
    let f : A ⊕ Unit → (Set.univ : Set A) ⊕ Fin 1 :=
      Sum.map (fun a => ⟨a, Set.mem_univ _⟩) (fun _ => 0)
    refine ⟨φ.relabel f, ?_⟩
    ext x
    have he : Sum.elim Subtype.val x ∘ f = Sum.elim id (fun _ => x 0) := by
      funext i
      cases i <;> rfl
    change φ.Realize (Sum.elim id (fun _ => x 0)) ↔ (φ.relabel f).Realize (Sum.elim Subtype.val x)
    rw [Formula.realize_relabel, he]
  obtain ⟨cells, hc, hS⟩ := hOM S hdef
  let idx := cells.equivFin.symm
  have hCode (i : Fin cells.card) : ∃ c : UnaryCellCode A, c.asSet id = (idx i).val :=
    exists_cell_code (hc _ (idx i).property)
  choose code hcode using hCode
  have hUnion : S = ⋃ i, (code i).asSet id := by
    rw [hS]
    ext x
    simp only [Set.mem_iUnion, hcode]
    constructor
    · rintro ⟨c, hc, hx⟩
      exact ⟨cells.equivFin ⟨c, hc⟩, by simpa only [idx, Equiv.symm_apply_apply]⟩
    · rintro ⟨i, hi⟩
      exact ⟨(idx i).val, (idx i).property, hi⟩
  let ψ := Formula.iSup fun i => unaryCellFormula F (code i)
  have hEval {J : Type z} [Field J] [LinearOrder J] [L.Structure J]
      (hJ : InterpretsOrderedFieldTerms (A := J) F) (e : A → J) (x : J) :
      ψ.Realize (Sum.elim e (fun _ => x)) ↔ x ∈ ⋃ i, (code i).asSet e := by
    simp only [ψ, Formula.realize_iSup, Set.mem_iUnion, realize_unaryCellFormula F hJ]
  let χ := (φ.iff ψ).iAlls Unit
  have hχ : χ.Realize (id : A → A) := by
    rw [Formula.realize_iAlls]
    intro x
    apply Formula.realize_iff.mpr
    have hx : x = (fun _ : Unit => x ()) := funext (fun i => by cases i; rfl)
    rw [hx, hEval hA id (x ()), ← hUnion]
    rfl
  have transfer {J : Type z} [Field J] [LinearOrder J] [L.Structure J]
      (hJ : InterpretsOrderedFieldTerms (A := J) F) (e : A ↪ₑ[L] J) (x : J) :
      φ.Realize (Sum.elim e (fun _ => x)) ↔ x ∈ ⋃ i, (code i).asSet e := by
    have h := (e.map_formula χ id).mpr hχ
    exact (Formula.realize_iff.mp ((Formula.realize_iAlls.mp h) (fun _ => x))).trans (hEval hJ e x)
  exact ⟨cells.card, code, transfer hK p, transfer hN q⟩

/-- O-minimality of the ordered field models of the base theory. -/
def IsOMinimalFieldTheory (T : L.Theory) : Prop :=
  ∀ (A : Type z) [Field A] [LinearOrder A] [IsStrictOrderedRing A] [L.Structure A] [A ⊨ T],
    IsOMinimal (K := A) L

set_option linter.style.haveILetI false in
/-- A shared cut over the old field determines a field embedding of
the actual generated extension in a universal o-minimal theory with QE. -/
theorem exists_simpleFieldEmbedding_of_model_cut
    {K N : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
    [Field N] [LinearOrder N] [IsStrictOrderedRing N] [L.Structure N]
    {T : L.Theory} [T.IsUniversal] [K ⊨ T] [N ⊨ T]
    (hK : InterpretsOrderedFieldTerms (A := K) F) (hN : InterpretsOrderedFieldTerms (A := N) F)
    (hOM : IsOMinimalFieldTheory.{u, v, z} T) (hQE : EliminatesQuantifiers T)
    (A : L.Substructure K) (k : A ↪[L] N) (a : K) (b : N)
    (hcut : ∀ c : A, ((c : K) < a ↔ k c < b) ∧ (a < (c : K) ↔ b < k c)) :
    ∃ f : Substructure.closure L (Set.range (Sum.elim (Subtype.val : A → K)
      (fun _ : Unit => a))) ↪[L] N,
      f ⟨a, Substructure.subset_closure ⟨.inr (), rfl⟩⟩ = b ∧
      ∀ c : A, f ⟨c.val, Substructure.subset_closure ⟨.inl c, rfl⟩⟩ = k c := by
  letI := fieldOnFieldSubstructure F hK A
  letI := strictOrderedRingOnFieldSubstructure F hK A
  have hA := interpretsOrderedFieldTerms_fieldSubstructure F hK A
  let p : A ↪ₑ[L] K := elementaryEmbeddingOfQE hQE A.subtype
  let q : A ↪ₑ[L] N := elementaryEmbeddingOfQE hQE k
  apply exists_simpleFieldEmbedding_of_same_cut A k a b hcut
  intro φ
  obtain ⟨n, cells, hLeft, hRight⟩ := exists_common_unary_cells F hA hK hN (hOM A) p q φ
  exact ⟨n, cells, hLeft a, hRight b⟩

set_option linter.style.haveILetI false in
/-- Universality and field QE make the old field an elementary
submodel. O-minimality then supplies the common cell descriptions, so
any prescribed representatives induce the chosen field adjunction. -/
theorem exists_fieldEmbedding_of_prescribed_representatives
    {E : Type*} {K N : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
    [Field N] [LinearOrder N] [IsStrictOrderedRing N] [L.Structure N]
    {T : L.Theory} [T.IsUniversal] [K ⊨ T] [N ⊨ T]
    (hK : InterpretsOrderedFieldTerms (A := K) F) (hN : InterpretsOrderedFieldTerms (A := N) F)
    (hOM : IsOMinimalFieldTheory.{u, v, z} T) (hQE : EliminatesQuantifiers T)
    (O : ValuationSubring K) (Q : ValuationSubring N)
    [L.Structure (Residue O)] [L.Structure (Residue Q)]
    (hO : IsOrderConvex O) (hQ : IsOrderConvex Q) (P : E → RV0 O → RV0 O) (PQ : E → RV0 Q → RV0 Q)
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (e : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))
    (t : S.carrier .rv) (ht : t.val ∉ rv O '' S.carrier .vf)
    (a : K) (b : N) (ha : rv O a = t.val) (hb : rv Q b = e.toEmbedding .rv t) :
    let A := vfReductOfSortedSubstructure O hO P S
    ∃ f : Substructure.closure L (Set.range (Sum.elim (Subtype.val : A → K)
      (fun _ : Unit => a))) ↪[L] N,
      f ⟨a, Substructure.subset_closure ⟨.inr (), rfl⟩⟩ = b ∧
      ∀ c : A, f ⟨c.val, Substructure.subset_closure ⟨.inl c, rfl⟩⟩ = e.toEmbedding .vf c := by
  let A := vfReductOfSortedSubstructure O hO P S
  let k := fieldEmbeddingOfSorted O Q hO hQ P PQ S e
  exact exists_simpleFieldEmbedding_of_model_cut F hK hN hOM hQE A k a b
    (prescribedLift_sameCut_of_sortedEmbedding O hO P Q hQ PQ e t ht ha hb)

end GeneralizedEuler.Section2
