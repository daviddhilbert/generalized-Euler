module

public import Section5.DefinablePullbackLabels
public import Section5.UnaryGradedObjects

/-! Split the labels of a prepared pullback by the nonzero field
leading terms. Each pattern gives an actual graded RV object. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

section ProjectedObject

variable {L : Language} {E : Type*} {Z : TCsort → Type z}
  {M : SortedStructure L E Z} {S : SortedSubstructure M} {a k : ℕ}

/-- A structure map obtained by reading specified coordinates.
All remaining coordinates of the tuple are kept as RV data. -/
@[expose] def projectedRVObject
    (D : Set (Fin a → Z .rv)) (select : Fin k → Fin a)
    (hD : isRVSet M S D)
    (nonzero : ∀ x ∈ D, ∀ i, x (select i) ≠ M.funMap .rvZero (fun j => j.elim0))
    (finite : ∀ y, {t ∈ D | t ∘ select = y}.Finite) :
    RVObject M S k where
  arity := a
  carrier := D
  definable := hD
  label x := x.val ∘ select
  graph := by
    have hd := isRVSet_precomp (J := Fin a ⊕ Fin k) Sum.inl hD
    have he := SortedDefinableOver.iInter (fun i : Fin k =>
      SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier)
        (Var := RVVariables (Fin a ⊕ Fin k)) .rv (.inl (select i)) (.inr i))
    convert hd.inter he using 1
    ext v
    simp only [rvGraph, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t,ht,hz⟩
      refine ⟨ht ▸ t.property, ?_⟩
      intro i
      exact (congrFun ht (select i)).symm.trans (congrFun hz i)
    · rintro ⟨ht,he⟩
      exact ⟨⟨_,ht⟩,rfl,funext he⟩
  nonzero x := nonzero x.val x.property
  finiteFibers y := by
    apply ((finite y).preimage (f := Subtype.val) Subtype.val_injective.injOn).subset
    intro t ht
    exact ⟨t.property,ht⟩

end ProjectedObject

section Canonical

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type}
  {n a k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable (D : Set (Fin n ⊕ I → RV0 O))
  (idx : Fin a ≃ Fin n ⊕ I) (support : Set (Fin n))

@[expose] def patternLabels : Set (Fin a → RV0 O) :=
  {t | t ∘ idx.symm ∈ D ∧ ∀ i, t (idx.symm (.inl i)) ≠ 0 ↔ i ∈ support}

theorem patternLabels_definable (hD : isRVSet 𝓜 S D) :
    isRVSet 𝓜 S (patternLabels O D idx support) := by
  classical
  let Q (i : Fin n) : Set (Fin a → RV0 O) :=
    {t | t (idx.symm (.inl i)) ≠ 0 ↔ i ∈ support}
  have ht (i : Fin n) : isRVSet 𝓜 S (Q i) := by
    have h := coordinate_zero_definable O hO power S (idx.symm (.inl i))
    by_cases hi : i ∈ support
    · unfold isRVSet at h ⊢
      convert h.compl using 1
      ext t
      simp [Q,hi]
    · have e : Q i = {t | t (idx.symm (.inl i)) = 0} := by
        ext t
        simp [Q,hi]
      rw [e]
      exact h
  have hd := isRVSet_precomp idx.symm hD
  have hQ := SortedDefinableOver.iInter ht
  unfold isRVSet
  convert hd.inter hQ using 1
  ext t
  simp only [patternLabels, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, Q]

variable (selected : Fin k ≃ support)

/-- Fill the deleted leading terms with zero, as in the degree
convention used by the lifting map. -/
def completeLead (y : Fin k → RV0 O) : Fin n → RV0 O := by
  classical
  exact fun i => if hi : i ∈ support then y (selected.symm ⟨i,hi⟩) else 0

@[expose] def patternSelect (i : Fin k) : Fin a :=
  idx.symm (.inl (selected i).val)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pattern_completeLead
    (t : Fin a → RV0 O) (ht : t ∈ patternLabels O D idx support) :
    completeLead O support selected (t ∘ patternSelect idx support selected) =
      fun i => t (idx.symm (.inl i)) := by
  classical
  funext i
  by_cases hi : i ∈ support
  · simp only [completeLead, dite_eq_left hi, Function.comp_apply, patternSelect, selected.apply_symm_apply]
  · have hz : t (idx.symm (.inl i)) = 0 := Classical.byContradiction (fun hn => hi ((ht.2 i).1 hn))
    simp only [completeLead, dite_eq_right hi, hz]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pattern_structure_finite
    (hfin : ∀ v : Fin n → RV0 O, {s : I → RV0 O | Sum.elim v s ∈ D}.Finite)
    (y : Fin k → RV0 O) :
    {t ∈ patternLabels O D idx support | t ∘ patternSelect idx support selected = y}.Finite := by
  let field := completeLead O support selected y
  let pack (s : I → RV0 O) := Sum.elim field s ∘ idx
  apply ((hfin field).image pack).subset
  rintro t ⟨ht, hy⟩
  have hv : field = fun i => t (idx.symm (.inl i)) := by
    have he := pattern_completeLead O D idx support selected t ht
    rw [hy] at he
    exact he
  have hs : Sum.elim field (t ∘ idx.symm ∘ Sum.inr) = t ∘ idx.symm := by
    funext i
    cases i with
    | inl i => exact congrFun hv i
    | inr _ => rfl
  refine ⟨t ∘ idx.symm ∘ Sum.inr, ?_, ?_⟩
  · change Sum.elim field (t ∘ idx.symm ∘ Sum.inr) ∈ D
    rw [hs]
    exact ht.1
  · funext j
    change Sum.elim field (t ∘ idx.symm ∘ Sum.inr) (idx j) = t j
    rw [hs]
    exact congrArg t (idx.symm_apply_apply j)

/-- The degree counts the active, nonzero leading terms. -/
@[expose] def patternRVObject (hD : isRVSet 𝓜 S D)
    (hfin : ∀ v : Fin n → RV0 O, {s : I → RV0 O | Sum.elim v s ∈ D}.Finite) :
    RVObject 𝓜 S k :=
  projectedRVObject (patternLabels O D idx support) (patternSelect idx support selected)
    (patternLabels_definable O hO power S D idx support hD)
    (fun _ ht i => (ht.2 (selected i).val).2 (selected i).property)
    (pattern_structure_finite O D idx support selected hfin)

end Canonical

end GeneralizedEuler.Section5
