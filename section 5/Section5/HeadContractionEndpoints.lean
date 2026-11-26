module

public import Section5.HeadContractionIteration
public import Section5.HeadStartZeroPatterns
public import Section5.RVPatternObjects

/-! The terminal family has a graded RV realization. The degree
counts the nonzero selected coordinates of each stratum. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {a k d : ℕ}

namespace RetainedFieldFamily

variable (B : RetainedFieldFamily M S 0 k) (tags : Fin a ≃ B.tags)

@[expose] def terminalLabels : Set (Fin a → RV0 O) :=
  {t | (Fin.elim0,t ∘ tags.symm) ∈ B.carrier}

@[expose] def terminalSelect : Fin k → Fin a := tags.symm ∘ B.select

theorem terminalLabels_definable : isRVSet M S (B.terminalLabels tags) := by
  let take : (s : TCsort) → MixedVariables 0 B.tags s → RVVariables (Fin a) s
    | .vf => Fin.elim0
    | .rv => tags.symm
  have h := B.definable.pullback_relabel take
  unfold isRVSet
  convert h using 1
  ext x
  have v : x .vf ∘ take .vf = (Fin.elim0 : Fin 0 → K) := Subsingleton.elim _ _
  change (Fin.elim0,x .rv ∘ tags.symm) ∈ B.carrier ↔ (x .vf ∘ take .vf,x .rv ∘ tags.symm) ∈ B.carrier
  rw [v]

theorem terminalLabels_finite (v : Fin k → RV0 O) :
    {t ∈ B.terminalLabels tags | t ∘ B.terminalSelect tags = v}.Finite :=
  (B.finiteFibers Fin.elim0 v).preimage
    (f := fun t => t ∘ tags.symm) (by
      intro x _ y _ eq
      funext i
      simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun eq (tags i))

/-- Realize a single support of the selected tuple as an RV object,
with the support enumerated by `keep`. All the terminal tags remain. -/
@[expose] def terminalPiece (keep : Fin d → Fin k) (zero : S.carrier .rv)
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0)) : RVObject M S d :=
  projectedRVObject (headStartStratum (B.terminalSelect tags) keep zero.val (B.terminalLabels tags))
    (B.terminalSelect tags ∘ keep)
    (headStartStratum_definable (B.terminalSelect tags) keep zero (B.terminalLabels_definable tags))
    (fun _ hx i => hzero ▸ headStartStratum_nonzero (B.terminalSelect tags) keep hx i)
    (headStartStratum_finite_indices (B.terminalSelect tags) keep zero.val (B.terminalLabels tags)
      (B.terminalLabels_finite tags))

/-- For the support of a given terminal label, its piece is uniquely
determined among enumerations up to equality of their ranges. -/
theorem terminal_piece_support (keep : Fin d → Fin k) (zero : S.carrier .rv)
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0)) {t : Fin a → RV0 O} :
    t ∈ (B.terminalPiece tags keep zero hzero).carrier ↔
      t ∈ B.terminalLabels tags ∧ {i | t (B.terminalSelect tags i) ≠ zero.val} = Set.range keep := by
  change (t ∈ B.terminalLabels tags ∧ ∀ i, t (B.terminalSelect tags i) ≠ zero.val ↔ i ∈ Set.range keep) ↔ _
  rw [Set.ext_iff]
  rfl

/-- Record the support as a finite tag and use its cardinality as the
degree of the corresponding object. -/
@[expose] def terminalGradedPiece (support : Finset (Fin k)) (zero : S.carrier .rv)
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0)) : GradedObject M S :=
  ⟨Fintype.card {i // i ∈ support},
    B.terminalPiece tags (Subtype.val ∘ (Fintype.equivFin {i // i ∈ support}).symm) zero hzero⟩

theorem terminalGradedPiece_mem (support : Finset (Fin k)) (zero : S.carrier .rv)
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0)) (t : Fin a → RV0 O) :
    t ∈ (B.terminalGradedPiece tags support zero hzero).2.carrier ↔
      t ∈ B.terminalLabels tags ∧ ∀ i, t (B.terminalSelect tags i) ≠ zero.val ↔ i ∈ support := by
  let e := (Fintype.equivFin {i // i ∈ support}).symm
  have range : Set.range (Subtype.val ∘ e) = (support : Set (Fin k)) := by
    ext i
    constructor
    · rintro ⟨j,rfl⟩
      exact (e j).property
    · intro hi
      refine ⟨e.symm ⟨i,hi⟩,?_⟩
      rw [Function.comp_apply,e.apply_symm_apply]
  change t ∈ (B.terminalPiece tags (Subtype.val ∘ e) zero hzero).carrier ↔ _
  rw [B.terminal_piece_support,range,Set.ext_iff]
  rfl

theorem terminal_existsUnique_piece (zero : S.carrier .rv)
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
    {t : Fin a → RV0 O} (ht : t ∈ B.terminalLabels tags) :
    ∃! support : Finset (Fin k), t ∈ (B.terminalGradedPiece tags support zero hzero).2.carrier := by
  classical
  let support := Finset.univ.filter (fun i => t (B.terminalSelect tags i) ≠ zero.val)
  have mem (i : Fin k) : i ∈ support ↔ t (B.terminalSelect tags i) ≠ zero.val := by simp [support]
  refine ⟨support,(B.terminalGradedPiece_mem tags support zero hzero t).2 ⟨ht,fun i => (mem i).symm⟩,?_⟩
  intro other h
  apply Finset.ext
  intro i
  exact (((B.terminalGradedPiece_mem tags other zero hzero t).1 h).2 i).symm.trans (mem i).symm

end RetainedFieldFamily

end GeneralizedEuler.Section5
