module

public import Section5.FiniteRVFieldGraphs
public import Section5.PairedUnaryGraphs

/-! A definable unary offset factors through the old RV labels.
The finite-center criterion bounds the image of this RV-to-VF map. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type} [Finite I]

local notation "𝓜" => canonicalStructure (L := L) O hO power

abbrev UnaryOffsetDefinable (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O))) :=
  DefinableRelation 𝓜 S.carrier
    (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I))
      (v : fieldAssignment 1 (CanonicalSort O)) => v .vf 0 = T.offset (a .rv) (rv O (a .vf 0)))

theorem unary_offset_label_graph (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (offsetGraph : UnaryOffsetDefinable O hO power S T) :
    DefinableRelation 𝓜 S.carrier (fun
      (t : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1 ⊕ I)))
      (v : fieldAssignment 1 (CanonicalSort O)) =>
      v .vf 0 = T.offset (t .rv ∘ Sum.inr) (t .rv (.inl 0))) := by
  have graph := (unaryLabelAssignment_definable O hO power S (H := I)).transpose.comp offsetGraph
  refine graph.congr ?_
  intro t v
  constructor
  · rintro ⟨a,h,offset⟩
    have tag : a .rv = t .rv ∘ Sum.inr := funext fun i => congrFun (congrFun h .rv) (.inr i)
    have lead : rv O (a .vf 0) = t .rv (.inl 0) := congrFun (congrFun h .rv) (.inl 0)
    rw [← tag,← lead]
    exact offset
  · intro h
    obtain ⟨x,hx⟩ := rv_surjective O (t .rv (.inl 0))
    let a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I)
      | .vf => fun _ => x
      | .rv => t .rv ∘ Sum.inr
    refine ⟨a,?_,?_⟩
    · funext s i
      cases s with
      | vf => exact i.elim
      | rv =>
        cases i with
        | inl i =>
          rw [Subsingleton.elim i (0 : Fin 1)]
          exact hx
        | inr i => rfl
    · change v .vf 0 = T.offset (t .rv ∘ Sum.inr) (rv O x)
      rw [hx]
      exact h

theorem unary_offset_finite_range
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (Fin 1 ⊕ I))
      (CenterTestAssignments S.carrier (Fin 1 ⊕ I)))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (defT : UnaryOffsetDefinable O hO power S T) :
    (Set.range (fun p : (I → RV0 O) × RV0 O => T.offset p.1 p.2)).Finite := by
  let f (t : Fin 1 ⊕ I → RV0 O) := T.offset (t ∘ Sum.inr) (t (.inl 0))
  let V := MixedVariables 1 (Fin 1 ⊕ I)
  let rename : ∀ s, SumVariables (RVVariables (Fin 1 ⊕ I)) (MixedVariables 1 Empty) s → V s
    | .vf => Sum.elim PEmpty.elim id
    | .rv => Sum.elim id Empty.elim
  have graph := unary_offset_label_graph O hO power S T defT
  have hf : SortedDefinableOver 𝓜 S.carrier {a : SortedAssignment (CanonicalSort O) V | a .vf 0 = f (a .rv)} :=
    graph.pullback_relabel rename
  obtain ⟨C,hC⟩ := finite_definable_rv_field_image O hO power S F minusOne hm hF sat immediate he small f hf
  apply ((C.finite_toSet).image Subtype.val).subset
  rintro _ ⟨p,rfl⟩
  exact hC ⟨Sum.elim (fun _ => p.2) p.1,rfl⟩

end GeneralizedEuler.Section5
