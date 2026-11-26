module

public import Section5.FieldArityPreparation
public import Section5.GradedLiftPresentation

/-! The lift presentation for a definable mixed set with finite fibers
over its field projection. -/

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
  {n : ℕ} {I : Type} [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power

omit [Finite I] in
private theorem mixed_domain_test_definable
    (A : Set (PreparationPoint O (Fin n) I))
    (hA : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables n I) | mixedTuple a ∈ A}) :
    PointTestsDefinable 𝓜 S {p : PreparationPoint O (Fin n) I × (Empty → RV0 O) | p.1 ∈ A} := by
  unfold PointTestsDefinable DefinableRelation
  exact hA.pullback_relabel (fun _ => Sum.inl)

/-- The fixed-base preparation sends a definable finite-fiber mixed
object onto a disjoint family of padded RV lifts. The field support
determines the degree of each component. -/
theorem mixed_set_is_graded_lift
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ n (J : Type), Finite J →
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n J))
        (BaseAssignments S.carrier (VerticalPairVariables n J)))
    (immediate : ∀ n (b : Fin n → K) (x y : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S b)
      (∀ c : B.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set (PreparationPoint O (Fin n) I))
    (hA : SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables n I) | mixedTuple a ∈ A})
    (finiteFibers : ∀ x : Fin n → K, {u | (x,u) ∈ A}.Finite) :
    ∃ (a : ℕ) (map : PreparationPoint O (Fin n) I → PreparationPoint O (Fin n) (Fin a)),
      PointMapDefinable 𝓜 S map ∧ Set.InjOn map A ∧ SpecialChain O (Fin n) A map ∧
      ∃ (degree : Set (Fin n) → ℕ) (selected : ∀ support, Fin (degree support) ≃ support)
        (U : (support : Set (Fin n)) → RVObject 𝓜 S (degree support)),
        ∃ pack : ∀ support, Fin a ≃ Fin (U support).arity,
          map '' A = {p | ∃ (support : Set (Fin n)) (t : (U support).carrier),
            t.val ∘ pack support = p.2 ∧
            (∀ j, rv O (p.1 (selected support j).val) = (U support).label t j) ∧
            (∀ i ∉ support, p.1 i = 0)} := by
  classical
  let G : PointTests O n I Empty := {p | p.1 ∈ A}
  have gDef : PointTestsDefinable 𝓜 S G := mixed_domain_test_definable O hO power S A hA
  have dom : testDomain G = A := by
    ext p
    exact ⟨fun ⟨_,hp⟩ => hp,fun hp => ⟨Empty.elim,hp⟩⟩
  have finiteG (x : Fin n → K) : {u | (x,u) ∈ testDomain G}.Finite := by
    rw [dom]
    exact finiteFibers x
  obtain ⟨P,special⟩ := preparedMap_of_definable O hO power S minusOne hm F hF sat immediate G gDef
  let := P.finiteTags
  let : Fintype P.tags := Fintype.ofFinite _
  let a := n + Fintype.card P.tags
  let idx : Fin a ≃ Fin n ⊕ P.tags := finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin P.tags).symm)
  let degree (support : Set (Fin n)) := Fintype.card support
  let selected (support : Set (Fin n)) : Fin (degree support) ≃ support :=
    (Fintype.equivFin support).symm
  let pack := packPrepared O hO power S P idx
  have packedSpecial := packed_preparation_special O hO power S P idx special
  rw [dom] at packedSpecial
  obtain ⟨U,encode,eq⟩ := prepared_lift_by_pattern O hO power S P idx degree selected gDef finiteG
  rw [dom,Set.image_image] at eq
  exact ⟨a,pack ∘ P.map,P.definable.comp (packPrepared_definable O hO power S P idx),
    ((packPrepared_injective O hO power S P idx).comp P.injective).injOn,
    packedSpecial,degree,selected,U,encode,eq⟩

end GeneralizedEuler.Section5
