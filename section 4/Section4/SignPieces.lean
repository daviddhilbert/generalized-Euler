module

public import Section4.LexicographicTags
public import Section2.RVSignCharts
import all Section2.RVSignCharts
import all Section2.RVMonomials
import all Section2.SortedStructure
import all Section4.FiniteScissors

/-! Fixed-sign pieces of an arbitrary definable subset of the nonzero RV torus. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {J : Language} {E K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [J.Structure K] (O : ValuationSubring K) [J.Structure (Residue O)] (hO : IsOrderConvex O)
  (P : E → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {k : ℕ} (U : Set (Fin k → RV0 O)) (hU : isRVSet _ S U)
  (minus : rv O (-1) ∈ S.carrier .rv)

def signPiece (b : Fin k → Bool) : Set (Fin k → RV0 O) := {x ∈ U | rvSignPattern O hO x = b}

theorem signPiece_unique (x : Fin k → RV0 O) (hx : x ∈ U) :
    ∃! b, x ∈ signPiece O hO U b :=
  ⟨_,⟨hx,rfl⟩,fun _ h => h.2.symm⟩

include hU in
theorem signPiece_definable (b : Fin k → Bool) : isRVSet _ S (signPiece O hO U b) := by
  let M := canonicalStructure (L := J) O hO P
  let Var := fun s => (S.carrier s : Type _) ⊕ RVVariables (Fin k) s
  let t (i : Fin k) : SortedTerm J E Var .rv := .var (.inr i)
  let test (i : Fin k) := (rvLessEqualFormula (rvZeroTerm (L := J) (E := E)) (t i)).neg
  have neg (i : Fin k) : isRVSet _ S {x | rvSignPattern O hO x i = true} := by
    refine ⟨test i,fun x => ?_⟩
    let := rvLinearOrder O hO
    change decide (x .rv i < 0) = true ↔ _
    rw [decide_eq_true_eq, SortedFormula.realize_neg]
    exact lt_iff_not_ge
  have guard (i : Fin k) : isRVSet _ S {x | rvSignPattern O hO x i = b i} := by
    cases hb : b i with
    | true => exact neg i
    | false =>
      unfold isRVSet
      convert (neg i).compl using 1
      ext x; change (_ = false) ↔ ¬(_ = true); exact Bool.eq_false_iff
  unfold isRVSet
  convert hU.inter (SortedDefinableOver.iInter guard) using 1
  ext x
  change (_ ∧ _ = b) ↔ _ ∧ x ∈ ⋂ i : Fin k, {x | rvSignPattern O hO (x .rv) i = b i}
  simp [funext_iff]

def positiveSignImage (b : Fin k → Bool) : Set (Fin k → RV0 O) :=
  changeRVSigns O b '' signPiece O hO U b

theorem positiveSignImage_positive (nz : ∀ x ∈ U, ∀ i, x i ≠ 0)
    (b : Fin k → Bool) (x : Fin k → RV0 O) (hx : x ∈ positiveSignImage O hO U b) (i : Fin k) : IsPositiveRV O (x i) := by
  obtain ⟨t,ht,rfl⟩ := hx
  exact (changeRVSigns_positive_iff O b hO t i).mpr ⟨nz t ht.1 i,(congrFun ht.2 i).symm⟩

include hU minus in
theorem signPiece_normalize (b : Fin k → Bool) :
    RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
      (signPiece O hO U b) (positiveSignImage O hO U b) := by
  let D := signPiece O hO U b
  have inj := Function.Involutive.injective (changeRVSigns_twice O b)
  let e := Equiv.Set.imageOfInjOn (changeRVSigns O b) D inj.injOn
  let M := canonicalStructure (L := J) O hO P
  let Var := RVVariables (Fin k ⊕ Fin k)
  let Vars := fun s => (S.carrier s : Type _) ⊕ Var s
  let input (i : Fin k) : SortedTerm J E Vars .rv := .var (.inr (.inl i))
  let negOne : SortedTerm J E Vars .rv := .var (.inl ⟨_,minus⟩)
  let t (i : Fin k) := if b i then rvMulTerm negOne (input i) else input i
  have ht (i : Fin k) (x : ∀ s, Var s → CanonicalSort O s) :
      (t i).realize M (fun s => Sum.elim Subtype.val (x s)) = changeRVSigns O b (x .rv ∘ Sum.inl) i := by
    cases hi : b i <;> simp [t,hi,changeRVSigns,signedRVNeg,input,negOne,M,realize_rvMulTerm,SortedTerm.realize]
  have hp : isRVSet M S {a : Fin k ⊕ Fin k → RV0 O | a ∘ Sum.inl ∈ D} :=
    isRVSet_precomp Sum.inl (signPiece_definable O hO P S U hU b)
  have graph := hp.inter (SortedDefinableOver.iInter (fun i : Fin k =>
    SortedDefinableOver.coordinate_eq_term (M := M) (A := S.carrier) (Var := Var) .rv (.inr i) (t i)))
  refine ⟨e,?_⟩
  convert graph using 1
  ext x
  change (∃ u : D, u.val = x .rv ∘ Sum.inl ∧ changeRVSigns O b u.val = x .rv ∘ Sum.inr) ↔
    _ ∧ x ∈ ⋂ i : Fin k, {a | a .rv (.inr i) = (t i).realize M (fun s => Sum.elim Subtype.val (a s))}
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,ht]
  exact ⟨fun ⟨u,hu,hy⟩ => ⟨hu ▸ u.property,fun i => hu ▸ (congrFun hy i).symm⟩,
    fun ⟨hu,hy⟩ => ⟨⟨_,hu⟩,rfl,funext fun i => (hy i).symm⟩⟩

end GeneralizedEuler.Section4
