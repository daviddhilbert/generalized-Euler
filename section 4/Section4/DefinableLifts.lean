module

public import Section4.Objects
public import Section2.DefinableAffineCharts
public import Section4.CoordinateChanges

/-! The fixed-base formulas for the affine lifts used by both tensor proofs. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
universe z
variable {L : Language} {F : Type*} {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO P))

theorem definable_monomial_map {m n : ℕ} (D : Set (Fin m → RV0 O))
    (hD : isRVSet _ S D) (A : Matrix (Fin n) (Fin m) F) (u : Fin n → S.carrier .rv) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P) S.carrier
      (rvGraph (fun x : D => rvAffineMonomial O P A (fun i => (u i).val) x.val)) := by
  let M := canonicalStructure (L := L) O hO P
  let V := RVVariables (Fin m ⊕ Fin n)
  let rename : ∀ s, RVVariables (Fin m) s → V s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  let domain : Set (∀ s, V s → CanonicalSort O s) := {v | v .rv ∘ Sum.inl ∈ D}
  have hd : SortedDefinableOver M S.carrier domain := hD.pullback_relabel rename
  let rows (i : Fin n) : Set (∀ s, V s → CanonicalSort O s) :=
    {v | v .rv (.inr i) = rvAffineMonomial O P A (fun k => (u k).val) (v .rv ∘ Sum.inl) i}
  have hr (i : Fin n) : SortedDefinableOver M S.carrier (rows i) := by
    let Var := fun s => (S.carrier s : Type z) ⊕ V s
    let intercept : SortedTerm L F Var .rv := .var (.inl (u i))
    let vars (j : Fin m) : SortedTerm L F Var .rv := .var (.inr (.inl j))
    let row := rvMonomialTerm intercept (A i) vars (Finset.univ : Finset (Fin m)).toList
    let out : SortedTerm L F Var .rv := .var (.inr (.inr i))
    refine ⟨.equal out row, fun x => ?_⟩
    change x .rv (.inr i) = _ ↔ x .rv (.inr i) = row.realize M (fun s => Sum.elim Subtype.val (x s))
    rw [realize_rvMonomialTerm]
    rfl
  convert hd.inter (SortedDefinableOver.iInter hr) using 1
  ext x
  change (∃ y : D, y.val = x .rv ∘ Sum.inl ∧ _ = x .rv ∘ Sum.inr) ↔ _
  simp only [Set.mem_inter_iff,Set.mem_iInter]
  constructor
  · rintro ⟨y,hy,he⟩
    refine ⟨show x .rv ∘ Sum.inl ∈ D from hy ▸ y.property, ?_⟩
    intro i
    change _ = rvAffineMonomial O P A _ (x .rv ∘ Sum.inl) i
    rw [← hy]; exact (congrFun he i).symm
  · rintro ⟨hy,he⟩
    exact ⟨⟨_,hy⟩,rfl,funext fun i => (he i).symm⟩

end GeneralizedEuler.Section4
