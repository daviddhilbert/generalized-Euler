module

public import Section2.RVReduct
public import Section2.ResidueFiber
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Definability of the monomial maps used for the fixed-base affine
trivialization in Lemma 2.29. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w a z

variable {L : Language.{u, v}} {E : Type w} {Var : TCsort → Type a}

def rvOneTerm : SortedTerm L E Var .rv :=
  .app .rvOne (fun i => i.elim0)

def rvZeroTerm : SortedTerm L E Var .rv :=
  .app .rvZero (fun i => i.elim0)

private def unaryRVArgs {X : TCsort → Type*} (x : X .rv) : SortedArgs X [.rv] :=
  fun i => by
    have h : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
    subst i
    exact x

def rvMulTerm (x y : SortedTerm L E Var .rv) : SortedTerm L E Var .rv :=
  .app .rvMul (Fin.cases x (fun i => unaryRVArgs y i))

def rvDivTerm (x y : SortedTerm L E Var .rv) : SortedTerm L E Var .rv :=
  rvMulTerm x (.app .rvInv (unaryRVArgs y))

def rvPowerTerm (e : E) (x : SortedTerm L E Var .rv) : SortedTerm L E Var .rv :=
  .app (.power e) (unaryRVArgs x)

/-- Equality of the unsigned values is a quantifier-free test in RV. -/
def rvSameUnsignedValueFormula (x y : SortedTerm L E Var .rv) : SortedFormula L E Var :=
  ((SortedFormula.equal x rvZeroTerm).conjunction (.equal y rvZeroTerm)).disjunction
    (.rel .residueNonzero (unaryRVArgs (rvDivTerm x y)))

theorem rvSameUnsignedValueFormula_isQF (x y : SortedTerm L E Var .rv) :
    (rvSameUnsignedValueFormula x y).IsQF := by
  exact .imp (SortedFormula.neg_isQF (SortedFormula.neg_isQF
    (.imp (.equal x rvZeroTerm) (SortedFormula.neg_isQF (.equal y rvZeroTerm)))))
    (.rel .residueNonzero _)

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

private theorem realize_rvMulTerm (x y : SortedTerm L E Var .rv)
    (a : ∀ s, Var s → CanonicalSort O s) :
    (rvMulTerm x y).realize (canonicalStructure O hO P) a =
      x.realize (canonicalStructure O hO P) a * y.realize (canonicalStructure O hO P) a := by
  rfl

theorem realize_rvDivTerm (x y : SortedTerm L E Var .rv)
    (a : ∀ s, Var s → CanonicalSort O s) :
    (rvDivTerm x y).realize (canonicalStructure O hO P) a =
      x.realize (canonicalStructure O hO P) a / y.realize (canonicalStructure O hO P) a := by
  exact (div_eq_mul_inv (x.realize (canonicalStructure O hO P) a : RV0 O)
    (y.realize (canonicalStructure O hO P) a)).symm

theorem realize_rvSameUnsignedValueFormula (x y : SortedTerm L E Var .rv)
    (a : ∀ s, Var s → CanonicalSort O s) :
    let M := canonicalStructure (L := L) O hO P
    (rvSameUnsignedValueFormula x y).realize M a ↔
      unsignedValue O (x.realize M a) = unsignedValue O (y.realize M a) := by
  let M := canonicalStructure (L := L) O hO P
  change (rvSameUnsignedValueFormula x y).realize M a ↔ _
  rw [rvSameUnsignedValueFormula, SortedFormula.realize_disjunction, SortedFormula.realize_conjunction]
  change ((x.realize M a = 0 ∧ y.realize M a = 0) ∨
      unsignedValue O ((rvDivTerm x y).realize M a) = 1) ↔ _
  rw [realize_rvDivTerm]
  exact (unsignedValue_eq_iff_div_residue O _ _).symm

/-- A tuple's unsigned value fiber is definable over any base containing
one representative of each coordinate value. -/
theorem definable_unsigned_value_fiber {A : ∀ s, Set (CanonicalSort O s)} {n : ℕ}
    (coordinates : Fin n → Var .rv) (reference : Fin n → A .rv) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P) A
      {a | ∀ i, unsignedValue O (a .rv (coordinates i)) = unsignedValue O (reference i).val} := by
  let V (i : Fin n) : Set (∀ s, Var s → CanonicalSort O s) :=
    {a | unsignedValue O (a .rv (coordinates i)) = unsignedValue O (reference i).val}
  have hV (i : Fin n) : SortedDefinableOver (canonicalStructure (L := L) O hO P) A (V i) := by
    let φ : SortedFormula L E (fun s => (A s : Type z) ⊕ Var s) :=
      rvSameUnsignedValueFormula (.var (.inr (coordinates i))) (.var (.inl (reference i)))
    refine ⟨φ, fun a => ?_⟩
    exact (realize_rvSameUnsignedValueFormula (L := L) (Var := fun s => (A s : Type z) ⊕ Var s) O hO P
      (.var (.inr (coordinates i))) (.var (.inl (reference i)))
      (fun s => Sum.elim Subtype.val (a s))).symm
  convert SortedDefinableOver.iInter hV using 1
  ext a
  simp only [V, Set.mem_iInter, Set.mem_ofPred_eq]

/-- The term representing an intercept times a finite monomial in RV. -/
def rvMonomialTerm {I : Type*} (u : SortedTerm L E Var .rv)
    (coeff : I → E) (x : I → SortedTerm L E Var .rv) (indices : List I) :
    SortedTerm L E Var .rv :=
  rvMulTerm u (indices.foldr (fun i t => rvMulTerm (rvPowerTerm (coeff i) (x i)) t) rvOneTerm)

theorem realize_rvMonomialTerm {I : Type*} (u : SortedTerm L E Var .rv)
    (coeff : I → E) (x : I → SortedTerm L E Var .rv) (indices : List I)
    (a : ∀ s, Var s → CanonicalSort O s) :
    let M := canonicalStructure O hO P
    (rvMonomialTerm u coeff x indices).realize M a =
      u.realize M a * (indices.map (fun i => P (coeff i) ((x i).realize M a))).prod := by
  let M := canonicalStructure (L := L) O hO P
  change (rvMonomialTerm u coeff x indices).realize M a =
    u.realize M a * (indices.map (fun i => P (coeff i) ((x i).realize M a))).prod
  rw [rvMonomialTerm, realize_rvMulTerm]
  congr 1
  induction indices with
  | nil => rfl
  | cons i r ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons, realize_rvMulTerm, ih]
    rfl

/-- The omitted coordinates of the affine lift divide by these monomials.
Their graphs use only the intercept representatives from the given base. -/
theorem definable_affine_division_coordinate {A : ∀ s, Set (CanonicalSort O s)}
    {I : Type*} (indices : List I) (coeff : I → E) (x : I → Var .rv)
    (u : A .rv) (input output : Var .rv) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P) A
      {a | a .rv output = a .rv input /
        (u.val * (indices.map (fun i => P (coeff i) (a .rv (x i)))).prod)} := by
  let U : SortedTerm L E (fun s => (A s : Type z) ⊕ Var s) .rv := .var (.inl u)
  let mono := rvMonomialTerm U coeff (fun i => .var (.inr (x i))) indices
  let t := rvDivTerm (.var (.inr input)) mono
  have h := SortedDefinableOver.coordinate_eq_term
    (M := canonicalStructure (L := L) O hO P) (A := A) .rv output t
  convert h using 1
  ext a
  simp only [t, mono, U, Set.mem_ofPred_eq, realize_rvDivTerm, realize_rvMonomialTerm,
    SortedTerm.realize, Sum.elim_inl, Sum.elim_inr]

theorem definable_rv_division_coordinate {A : ∀ s, Set (CanonicalSort O s)}
    (u : A .rv) (input output : Var .rv) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P) A
      {a | a .rv output = a .rv input / u.val} := by
  simpa only [List.map_nil, List.prod_nil, mul_one (u.val : RV0 O)] using
    (definable_affine_division_coordinate (L := L) O hO P ([] : List Empty)
      Empty.elim Empty.elim u input output)

section Embeddings

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure F]
  (Q : ValuationSubring F) [L.Structure (Residue Q)] (hQ : IsOrderConvex Q) (PQ : E → RV0 Q → RV0 Q)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
  (e : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))

/-- A sorted embedding preserves equality of unsigned values on its
named RV elements. -/
theorem unsignedValue_eq_iff_of_sortedEmbedding (s t : S.carrier .rv) :
    unsignedValue O s.val = unsignedValue O t.val ↔
      unsignedValue Q (e.toEmbedding .rv s) = unsignedValue Q (e.toEmbedding .rv t) := by
  let v : ∀ b, RVVariables (Fin 2) b → S.carrier b
    | .vf => PEmpty.elim
    | .rv => Fin.cases s (fun _ => t)
  let φ : SortedFormula L E (RVVariables (Fin 2)) := rvSameUnsignedValueFormula (.var 0) (.var 1)
  have hφ : φ.IsQF := rvSameUnsignedValueFormula_isQF _ _
  have h := (S.inclusion.realize_qf hφ v).trans (e.realize_qf hφ v).symm
  simp only [φ, realize_rvSameUnsignedValueFormula, SortedTerm.realize,
    SortedEmbedding.mapAssignment_apply, SortedSubstructure.inclusion_apply] at h
  exact h

/-- The new-value test in Theorem 2.16 is preserved by the sorted map,
with the target old field taken to be the image of the same base. -/
theorem has_old_value_iff_of_sortedEmbedding (t : S.carrier .rv) :
    (∃ x : S.carrier .vf, unsignedValue O t.val = O.valuation x.val) ↔
      ∃ x : S.carrier .vf, unsignedValue Q (e.toEmbedding .rv t) = Q.valuation (e.toEmbedding .vf x) := by
  refine exists_congr fun x => ?_
  let s := S.structureOn.rvMap x
  have hLeft : s.val = rv O x.val := by
    have h := S.inclusion.map_rv x
    rw [canonicalStructure_rvMap, SortedSubstructure.inclusion_apply,
      SortedSubstructure.inclusion_apply] at h
    exact h
  have hRight : e.toEmbedding .rv s = rv Q (e.toEmbedding .vf x) := by
    have h := e.map_rv x
    rwa [canonicalStructure_rvMap] at h
  have h := unsignedValue_eq_iff_of_sortedEmbedding O hO P Q hQ PQ S e t s
  rwa [hLeft, hRight, unsignedValue_rv, unsignedValue_rv] at h

end Embeddings

end GeneralizedEuler.Section2
