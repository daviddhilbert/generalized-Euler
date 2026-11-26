module

public import Section5.UnaryInitialPreparation
public import Section5.UnaryChartAfterPreparation

/-! From a finite fixed-base disc-chart partition, prepare the
source so each fiber lies in one chart and has constant target label. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I J : Type} {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
  (e : A ≃ B)

structure UnaryChartPartition (H : Type) where
  piece : H → Set (K × (I → RV0 O))
  cover : ∀ x : A, ∃ i, x.val ∈ piece i
  definable : ∀ i, UnaryPullbackDefinable O hO power S (piece i)
  charts : ∀ (i : H) (t : I → RV0 O) (u : J → RV0 O),
    ∃ (D E : Set K) (f g : K → K), DiscToDiscOn O D E f g ∧
      ∀ x : A, x.val ∈ piece i → x.val.2 = t → (e x).val.2 = u →
        x.val.1 ∈ D ∧ f x.val.1 = (e x).val.1

variable [Finite I] [Finite J]

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "cert" => fun _ T => UnaryOffsetDefinable O hO power S T

theorem normalize_unary_source {H : Type} [Finite H]
    (P : UnaryChartPartition O hO power S e H)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ H : Type, Finite H → RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier H)
      (CenterTestAssignments S.carrier H))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t)
    (defA : UnaryPullbackDefinable O hO power S A) (full : IsUnaryPullback O A)
    (graph : UnaryMixedGraphDefinable O hO power S e) :
    ∃ (I' : Type) (_ : Finite I') (A' : Set (K × (I' → RV0 O))) (t : A ≃ A'),
      EncodedFocusChain O cert A A' t ∧ UnaryMixedGraphDefinable O hO power S t ∧ IsUnaryPullback O A' ∧
      UnaryDiscCharts O (t.symm.trans e) ∧
      Contractible (unaryMixedLabel O ∘ Subtype.val) (unaryMixedLabel O ∘ Subtype.val) (t.symm.trans e) := by
  classical
  let := Fintype.ofFinite H
  have part (i : H) := finite_centers_of_definable O hO power S minusOne hm F hF (sat I inferInstance)
    immediate (P.piece i) (P.definable i)
  choose C hC using part
  obtain ⟨E,hE⟩ := inverse_label_tests_at_finite_centers O hO power S e.symm
    (unaryMixedGraph_symm O hO power S e graph) minusOne hm F hF (sat _ inferInstance) immediate
  let all := E ∪ Finset.univ.biUnion C
  let center (c : S.carrier .vf) : CenterTest O I := fun _ => c.val
  let tests := all.toList.map center
  have defTests (d) (hd : d ∈ tests) : CenterTestDefinable O hO power S d := by
    obtain ⟨c,_,rfl⟩ := List.mem_map.1 hd
    exact SortedDefinableOver.coordinate_eq_parameter (M := 𝓜) (A := S.carrier)
      (Var := SumVariables (RVVariables I) (MixedVariables 1 Empty)) .vf (.inr 0) c
  obtain ⟨I',fi,A',t,ht,defT,full',decides⟩ :=
    definable_center_preparation_on_pullback O hO power S F minusOne hm hF A defA full tests defTests
  have test (x y : A) (same : unaryMixedLabel O (t x).val = unaryMixedLabel O (t y).val)
      (c : S.carrier .vf) (hc : c ∈ all) : rv O (x.val.1-c.val) = rv O (y.val.1-c.val) :=
    decides x y same (center c) (List.mem_map.2 ⟨c,Finset.mem_toList.2 hc,rfl⟩)
  have origTag (x y : A) (same : unaryMixedLabel O (t x).val = unaryMixedLabel O (t y).val) : x.val.2 = y.val.2 :=
    congrArg (fun p : RV0 O × (I → RV0 O) => p.2) (ht.refines_labels O x y same)
  have labels (x y : A) (same : unaryMixedLabel O (t x).val = unaryMixedLabel O (t y).val) :
      unaryMixedLabel O (e x).val = unaryMixedLabel O (e y).val := by
    exact hE x y (origTag x y same) (fun c hc => test x y same c (Finset.mem_union_left _ hc))
  refine ⟨I',fi,A',t,ht,defT,full',?_,?_⟩
  · apply unary_charts_after_preparation O t e ht full'
    intro x
    obtain ⟨i,hi⟩ := P.cover x
    obtain ⟨D,E,f,g,h,agree⟩ := P.charts i x.val.2 (e x).val.2
    refine ⟨D,E,f,g,h,?_⟩
    intro y same
    have m : (y.val.1,x.val.2) ∈ P.piece i := (hC i x.val.1 y.val.1 x.val.2 (fun c hc =>
      test x y same.symm c (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i,Finset.mem_univ _,hc⟩)))).1 hi
    have mem : y.val ∈ P.piece i := by
      change (y.val.1,y.val.2) ∈ P.piece i
      rw [origTag y x same]
      exact m
    exact agree y mem (origTag y x same) (congrArg (fun t : RV0 O × (J → RV0 O) => t.2) (labels y x same))
  · intro x y same
    obtain ⟨x,rfl⟩ := t.surjective x
    obtain ⟨y,rfl⟩ := t.surjective y
    change unaryMixedLabel O (e (t.symm (t x))).val = unaryMixedLabel O (e (t.symm (t y))).val
    rw [t.symm_apply_apply,t.symm_apply_apply]
    exact labels x y same

end GeneralizedEuler.Section5
