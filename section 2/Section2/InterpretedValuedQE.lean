module

public import Section2.InterpretedValuedTheory
public import Section2.DirectedSubstructure

/-! The Shoenfield test for the interpreted theory reduces to the
prescribed leading-term representative step. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w a z z'

variable {L : Language.{u, v}} {E : Type w}
  (I : QuotientInterpretation (convexLanguage L) L E) (minusOne : L.Term Empty)
  {T : (convexLanguage L).Theory} (hQE : EliminatesQuantifiers T)

include hQE

/-- The named tuple in a VF-generated substructure has common field
representatives. Its complete sorted type is determined by field QE. -/
theorem realize_iff_of_interpreted_vfGenerated
    {X : TCsort → Type z} {Y : TCsort → Type z'} {M : SortedStructure L E X} {N : SortedStructure L E Y}
    [Nonempty (X .vf)] [Nonempty (Y .vf)]
    (hM : ∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize M)
    (hN : ∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize N)
    (S : SortedSubstructure M) (e : SortedEmbedding S.structureOn N)
    (hgen : S.structureOn.IsVFGenerated) {Var : TCsort → Type a}
    (φ : SortedFormula L E Var) (x : ∀ s, Var s → S.carrier s) :
    φ.realize M (fun s i => (x s i).val) ↔ φ.realize N (fun s i => e.toEmbedding s (x s i)) := by
  let := valuedStructureOfSorted M (recoveredRing M minusOne)
  let := valuedStructureOfSorted N (recoveredRing N minusOne)
  let := valuedStructureOfSorted S.structureOn (recoveredRing S.structureOn minusOne)
  obtain ⟨hTM, RM, hRM⟩ := (models_interpretedValuedTheory_iff M I minusOne T).mp hM
  obtain ⟨hTN, RN, hRN⟩ := (models_interpretedValuedTheory_iff N I minusOne T).mp hN
  let := hTM
  let := hTN
  let p := valuedEmbeddingOfSorted S.inclusion minusOne
  let q := valuedEmbeddingOfSorted e minusOne
  let r (i : Var .rv) : S.carrier .vf := (hgen (x .rv i)).choose
  have hr (i : Var .rv) : S.structureOn.rvMap (r i) = x .rv i := (hgen (x .rv i)).choose_spec
  let rep : TaggedVar Var → S.carrier .vf
    | ⟨.vf, i⟩ => x .vf i
    | ⟨.rv, i⟩ => r i
  have hLeft : RM.assignment (p ∘ rep) = fun s i => (x s i).val := by
    funext s i
    rw [RealizesQuotientInterpretation.assignment_apply, hRM]
    cases s with
    | vf =>
      change p (x .vf i) = (x .vf i).val
      rw [valuedEmbeddingOfSorted_apply, SortedSubstructure.inclusion_apply]
    | rv =>
      change M.rvMap (p (r i)) = (x .rv i).val
      rw [valuedEmbeddingOfSorted_apply, ← S.inclusion.map_rv, hr, SortedSubstructure.inclusion_apply]
  have hRight : RN.assignment (q ∘ rep) = fun s i => e.toEmbedding s (x s i) := by
    funext s i
    rw [RealizesQuotientInterpretation.assignment_apply, hRN]
    cases s with
    | vf => exact valuedEmbeddingOfSorted_apply e minusOne (x .vf i)
    | rv =>
      change N.rvMap (q (r i)) = e.toEmbedding .rv (x .rv i)
      rw [valuedEmbeddingOfSorted_apply, ← e.map_rv, hr]
  have h := sortedFormula_iff_of_common_field_representatives I hQE RM RN p q rep φ
  rwa [hLeft, hRight] at h

/-- Theorem 2.16 reduces to adjoining one field representative while
keeping the existing RV embedding. Both the VF-generated case and the
compactness step apply to the first-order interpreted theory. -/
theorem exists_qf_equivalent_of_interpreted_representative_step
    (hStep : ∀ {X Y : TCsort → Type (max u v w a)}
      {M : SortedStructure L E X} {N : SortedStructure L E Y},
      (∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize M) →
      (∀ φ ∈ interpretedValuedTheory I minusOne T, φ.realize N) →
      ∀ {R : Set (X .rv)} (B : FixedRVLift M N R) (t : X .rv), t ∈ R →
      t ∉ M.rvMap '' B.source.carrier .vf →
      ∃ C : FixedRVLift M N R, B ≤ C ∧ t ∈ M.rvMap '' C.source.carrier .vf)
    {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : (interpretedValuedTheory I minusOne T).PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  let T' := interpretedValuedTheory I minusOne T
  apply T'.exists_qf_equivalent_of_generated_partial_elementarity _ φ
  intro W P Q e he ψ
  let S := P.model.termGenerated P.point
  let A : FixedRVLift P.model Q.model (S.carrier .rv) := ⟨S, rfl, e⟩
  let := P.nonempty .vf
  let := Q.nonempty .vf
  let x := P.model.termGeneratedAssignment P.point
  have h := A.realize_iff_of_vfGenerated_extension
    (fun B _ t ht hn => hStep P.models Q.models B t ht hn)
    (fun B _ hB _ θ y => realize_iff_of_interpreted_vfGenerated I minusOne hQE
      P.models Q.models B.source B.embedding hB θ y) ψ x
  change (ψ.realize P.model (fun s i => (x s i).val) ↔
    ψ.realize Q.model (fun s i => A.embedding.toEmbedding s (x s i))) at h
  rw [show (fun s i => A.embedding.toEmbedding s (x s i)) = Q.point from funext fun s => funext (he s)] at h
  exact h

end GeneralizedEuler.Section2
