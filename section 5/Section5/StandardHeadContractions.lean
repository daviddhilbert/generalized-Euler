module

public import Section5.HeadContractionEndpoints

/-! A contraction in any specified order reaches a finite graded
RV family over the fixed base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- The hypotheses used uniformly for the fixed-base unary
preparations with the already retained coordinates as parameters. -/
structure HeadPreparationHypotheses where
  minusOne : L.Term Empty
  minusOne_realizes : minusOne.realize (Empty.elim : Empty → K) = -1
  fieldTerms : FieldTerms (convexLanguage L)
  fieldTerms_realize : letI := convexStructure O L; InterpretsFieldTerms (K := K) fieldTerms
  saturated : ∀ (n : ℕ) (I : Type), Finite I →
    RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n I))
      (BaseAssignments S.carrier (VerticalPairVariables n I))
  immediate : ∀ (n : ℕ) (b : Fin n → K) (x y : K),
    let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S b)
    (∀ c : B.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
    ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
      (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t

variable {O hO power S} {n k : ℕ}

theorem standard_head_contraction_exists
    (hyp : HeadPreparationHypotheses (L := L) O hO power S)
    (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S n k)
    (order : Equiv.Perm (Fin n)) :
    ∃ B : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 0 (k+n),
      HeadContractionRun (A.permuteVF order) B :=
  HeadContractionRun.exists_run (fun m _ D =>
    head_contraction_data_exists hO power S hyp.minusOne hyp.minusOne_realizes hyp.fieldTerms hyp.fieldTerms_realize
      D (hyp.saturated m D.tags D.finiteTags) (hyp.immediate m)) (A.permuteVF order)

/-- An output includes its provenance as a run, all terminal tags,
and an RV object for each zero pattern of the selected coordinates. -/
structure StandardHeadOutput
    (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S n k)
    (order : Equiv.Perm (Fin n)) where
  terminal : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 0 (k+n)
  run : HeadContractionRun (A.permuteVF order) terminal
  arity : ℕ
  tags : Fin arity ≃ terminal.tags

namespace StandardHeadOutput

variable {A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S n k}
  {order : Equiv.Perm (Fin n)} (B : StandardHeadOutput A order)

@[expose] def pieces (support : Finset (Fin (k+n))) :
    GradedObject (canonicalStructure (L := L) O hO power) S :=
  B.terminal.terminalGradedPiece B.tags support
    ⟨(𝓜).funMap .rvZero (fun i => i.elim0),S.closed .rvZero _ (fun i => i.elim0)⟩ rfl

theorem existsUnique_piece {t : Fin B.arity → RV0 O} (ht : t ∈ B.terminal.terminalLabels B.tags) :
    ∃! support : Finset (Fin (k+n)), t ∈ (B.pieces support).2.carrier :=
  B.terminal.terminal_existsUnique_piece B.tags
    ⟨(𝓜).funMap .rvZero (fun i => i.elim0),S.closed .rvZero _ (fun i => i.elim0)⟩ rfl ht

end StandardHeadOutput

theorem standard_head_output_exists
    (hyp : HeadPreparationHypotheses (L := L) O hO power S)
    (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S n k)
    (order : Equiv.Perm (Fin n)) : Nonempty (StandardHeadOutput A order) := by
  obtain ⟨B,run⟩ := standard_head_contraction_exists hyp A order
  let := B.finiteTags
  let := Fintype.ofFinite B.tags
  exact ⟨⟨B,run,Fintype.card B.tags,(Fintype.equivFin B.tags).symm⟩⟩

end GeneralizedEuler.Section5
