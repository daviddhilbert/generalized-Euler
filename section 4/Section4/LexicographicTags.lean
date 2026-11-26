module

public import Section4.TaggedObjects
public import Section2.RVMonomials
import all Section2.RVMonomials
import all Section2.SortedStructure

public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {J : Language} {E K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [J.Structure K] (O : ValuationSubring K) [J.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : E → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

theorem canonical_lt_coordinates {I : Type} (i j : I) :
    isRVSet _ S {x : I → RV0 O | (rvLinearOrder O hO).lt (x i) (x j)} := by
  let Var := fun s => (S.carrier s : Type _) ⊕ RVVariables I s
  let x : SortedTerm J E Var .rv := .var (.inr i)
  let y : SortedTerm J E Var .rv := .var (.inr j)
  refine ⟨(rvLessEqualFormula y x).neg,fun t => ?_⟩
  let := rvLinearOrder O hO
  rw [SortedFormula.realize_neg]
  change t .rv i < t .rv j ↔ ¬t .rv j ≤ t .rv i
  exact lt_iff_not_ge

theorem canonical_lex_definable {n} :
    let := rvLinearOrder O hO
    isRVSet _ S {x : Fin n ⊕ Fin n → RV0 O | toLex (x ∘ Sum.inr) < toLex (x ∘ Sum.inl)} := by
  let := rvLinearOrder O hO
  let D (i : Fin n) : Set (Fin n ⊕ Fin n → RV0 O) :=
    {x | (∀ j < i, x (.inr j) = x (.inl j)) ∧ x (.inr i) < x (.inl i)}
  have hd (i) : isRVSet _ S (D i) := by
    have ht := SortedDefinableOver.iInter (fun j : {j : Fin n // j < i} =>
      SortedDefinableOver.coordinate_eq (M := canonicalStructure (L := J) O hO P) (A := S.carrier)
        (Var := RVVariables (Fin n ⊕ Fin n)) .rv (.inr j.val) (.inl j.val))
    unfold isRVSet
    convert ht.inter (canonical_lt_coordinates O hO P S (.inr i) (.inl i)) using 1
    ext t
    change ((∀ j < i, _ = _) ∧ _) ↔ _
    simp
  convert isRVSet_iUnion hd using 2
  ext x
  change (∃ i, (∀ j < i, x (.inr j) = x (.inl j)) ∧ x (.inr i) < x (.inl i)) ↔ x ∈ ⋃ i, D i
  rw [Set.mem_iUnion]; rfl

theorem canonical_tagged_presentation {k} (U : RVObject _ S k)
    (sat : ∀ D : ℕ → Set (Fin k → RV0 O), (∀ i, isRVSet _ S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i) :
    ∃ (N : ℕ) (V : Fin N → RVObject _ S k), (∀ i, (V i).arity = k) ∧
      (∀ i, ∃ h : (V i).arity = k, ∀ x : (V i).carrier, (V i).label x = fun j => x.val (Fin.cast h.symm j)) ∧
      objectClass _ S ⟨k,U⟩ = ∑ i, objectClass _ S ⟨k,V i⟩ := by
  let := rvLinearOrder O hO
  exact U.tagged_presentation (fun x y => toLex x < toLex y) (fun a b => lt_trans a b)
    (fun x => lt_irrefl _) (fun x y ne => lt_or_gt_of_ne (fun he => ne (toLex.injective he)))
    (canonical_lex_definable O hO P S) sat

end GeneralizedEuler.Section4
