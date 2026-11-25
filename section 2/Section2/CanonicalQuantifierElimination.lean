module

public import Section2.InterpretedValuedQE
public import Section2.GeneratedRVAdjunction

/-! Quantifier elimination from the model presentation and the
T-convex inputs on a simple field adjunction. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w a z

variable {L : Language.{u, v}} {E : Type w} [Field E]
  (T : L.Theory) (Tconvex : (convexLanguage L).Theory)
  (terms : OrderedFieldTerms L) (graph : E → L.Formula (Fin 2))

set_option linter.style.haveILetI false in
/-- The ordered valued-field and named-power data of a canonical model
of the underlying proper T-convex theory. -/
structure CanonicalQEModel (K : Type z) where
  field : Field K
  order : LinearOrder K
  orderedRing : letI := field; letI := order; IsStrictOrderedRing K
  languageStructure : L.Structure K
  models : letI := languageStructure; K ⊨ T
  orderedTerms : letI := field; letI := order; letI := languageStructure
    InterpretsOrderedFieldTerms (A := K) terms
  ring : letI := field; ValuationSubring K
  convex : letI := field; letI := order; IsOrderConvex ring
  modelsValued : letI := field; letI := languageStructure; letI := convexStructure ring L
    K ⊨ Tconvex
  residueStructure : letI := field; L.Structure (Residue ring)
  powers : letI := field; letI := order; letI := orderedRing; letI := languageStructure
    NamedFieldPowers K graph
  rvPowers : letI := field; letI := order; letI := orderedRing; letI := languageStructure
    NamedRVPowers ring powers.pow

variable {T Tconvex terms graph}

set_option linter.style.haveILetI false in
/-- The canonical sorted expansion of the proper valued field. -/
@[expose]
def CanonicalQEModel.structureOn {K : Type z} (d : CanonicalQEModel T Tconvex terms graph K) :
    letI := d.field
    SortedStructure L E (CanonicalSort d.ring) := by
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  exact canonicalStructure d.ring d.convex d.rvPowers.pow

set_option linter.style.haveILetI false in
/-- The literature data for all fresh representative adjunctions
between these two proper valued-field models. -/
@[expose]
def CanonicalQEModel.hasAdjunctionInputs {K F : Type z}
    (d : CanonicalQEModel T Tconvex terms graph K)
    (e : CanonicalQEModel T Tconvex terms graph F) : Prop :=
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := e.field
  letI := e.order
  letI := e.orderedRing
  letI := e.languageStructure
  letI := e.residueStructure
  ∀ {R : Set (RV0 d.ring)} (A : FixedRVLift d.structureOn e.structureOn R)
    (a : PositiveField K) (b : F) (s : A.source.carrier .rv),
    s.val ∉ rv d.ring '' A.source.carrier .vf →
    rv d.ring a.val = s.val → rv e.ring b = A.embedding.toEmbedding .rv s →
    HasOneGeneratorTConvexInputs (T := T) terms d.orderedTerms e.orderedTerms
      d.ring e.ring d.powers e.powers d.rvPowers e.rvPowers d.convex e.convex A a b

set_option linter.style.haveILetI false in
/-- Theorem 2.16 for the uniform interpreted theory, from canonical
presentation of its models and the stated one-generator rank and
residue inputs. It uses the generated-field adjunction directly. -/
theorem exists_qf_equivalent_of_tconvex_adjunction_inputs
    [T.IsUniversal] (hQE : EliminatesQuantifiers T) (hQEconvex : EliminatesQuantifiers Tconvex)
    (hOM : IsOMinimalFieldTheory.{u, v, max u v w a} T)
    (I : QuotientInterpretation (convexLanguage L) L E) (minusOne : L.Term Empty)
    (hModel : ∀ {X : TCsort → Type (max u v w a)} (M : SortedStructure L E X),
      (∀ φ ∈ interpretedValuedTheory I minusOne Tconvex, φ.realize M) →
      ∃ d : CanonicalQEModel T Tconvex terms graph (X .vf),
        Nonempty (SortedIsomorphism M d.structureOn))
    (hInputs : ∀ {K F : Type (max u v w a)}
      (d : CanonicalQEModel T Tconvex terms graph K)
      (e : CanonicalQEModel T Tconvex terms graph F), d.hasAdjunctionInputs e)
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : (interpretedValuedTheory I minusOne Tconvex).PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  apply exists_qf_equivalent_of_interpreted_representative_step I minusOne hQEconvex _ φ
  intro X Y M N hM hN R A t ht hFresh
  obtain ⟨d, ⟨i⟩⟩ := hModel M hM
  obtain ⟨e, ⟨j⟩⟩ := hModel N hN
  apply A.exists_extension_of_isomorphic_step i j t ht hFresh
  intro W B s hs hsFresh
  letI := d.field
  letI := d.order
  letI := d.orderedRing
  letI := d.languageStructure
  letI := d.residueStructure
  letI := d.models
  letI := e.field
  letI := e.order
  letI := e.orderedRing
  letI := e.languageStructure
  letI := e.residueStructure
  letI := e.models
  have hn : s ∉ rv d.ring '' B.source.carrier .vf := by
    rwa [← show d.structureOn.rvMap = rv d.ring from funext (canonicalStructure_rvMap d.ring d.convex _)]
  obtain ⟨C, hBC, hC⟩ := exists_fixedRVExtension_of_tconvex_inputs terms
    d.orderedTerms e.orderedTerms d.ring e.ring d.powers e.powers d.rvPowers e.rvPowers
    d.convex e.convex B hOM hQE (hInputs d e B) s hs hn
  refine ⟨C, hBC, ?_⟩
  simpa only [CanonicalQEModel.structureOn, canonicalStructure_rvMap] using hC

end GeneralizedEuler.Section2
