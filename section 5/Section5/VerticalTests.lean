module

public import Section5.DescendedVerticalGraph
public import Section5.PointTests

/-! Translate between a test on (n+1) field coordinates and its
descended test on (n) coordinates with the head label retained. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language UnaryPreparation

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n : ℕ} {I J C : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def verticalForm (G : PointTests O (n+1) I J) :
    Set (K × ((Fin n → K) × (I ⊕ J → RV0 O))) :=
  {p | ((Fin.cons p.1 p.2.1, p.2.2 ∘ Sum.inl), p.2.2 ∘ Sum.inr) ∈ G}

theorem verticalForm_definable {G : PointTests O (n+1) I J}
    (hG : PointTestsDefinable 𝓜 S G) :
    SortedDefinableOver 𝓜 S.carrier
      {a : SortedAssignment (CanonicalSort O) (VerticalVariables n (I ⊕ J)) |
        (a .vf (.inl ()), a .vf ∘ Sum.inr, a .rv) ∈ verticalForm O G} := by
  let rename : ∀ s, SumVariables (MixedVariables (n+1) I) (RVVariables J) s →
      VerticalVariables n (I ⊕ J) s
    | .vf => Sum.elim (Fin.cases (.inl ()) Sum.inr) PEmpty.elim
    | .rv => id
  unfold PointTestsDefinable DefinableRelation at hG
  convert hG.pullback_relabel rename using 1
  ext a
  have hv : Fin.cons (a .vf (.inl ())) (a .vf ∘ Sum.inr) =
      (a .vf ∘ rename .vf ∘ Sum.inl) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change ((Fin.cons (a .vf (.inl ())) (a .vf ∘ Sum.inr), a .rv ∘ Sum.inl), a .rv ∘ Sum.inr) ∈ G ↔ _
  rw [hv]
  rfl

/-- The head history is carried in the input's RV tuple and the
expected output remains a separate RV tuple. -/
@[expose] def descendedTest {k : ℕ}
    (P : (Fin n → K) → UnaryPreparation O (PreparationLabels O (RV0 O) k))
    (G : PointTests O (n+1) I J) : PointTests O n (I ⊕ HistoryIndex k) J :=
  {p | ∃ x, ((Fin.cons x p.1.1, p.1.2 ∘ Sum.inl), p.2) ∈ G ∧
    (P p.1.1).label x = decodeHistory O k (p.1.2 ∘ Sum.inr)}

theorem descendedTest_definable {G : PointTests O (n+1) I J}
    (hG : PointTestsDefinable 𝓜 S G)
    (center : (Fin n → K) → Option C → K) (cs : List C)
    (hmap : SortedDefinableOver 𝓜 S.carrier
      {v : SortedAssignment (CanonicalSort O) (HistoryGraphVariables n cs.length) |
        (centerPreparation (O := O) (center (v .vf ∘ Sum.inr)) cs).map (v .vf (.inl 0)) =
          (v .vf (.inl 1), decodeHistory O cs.length (v .rv))}) :
    PointTestsDefinable 𝓜 S (descendedTest O (fun b => centerPreparation (O := O) (center b) cs) G) := by
  have h := descended_vertical_graph_definable O hO power S (verticalForm O G)
    (verticalForm_definable O hO power S hG) center cs hmap
  let V := SumVariables (MixedVariables n (I ⊕ HistoryIndex cs.length)) (RVVariables J)
  let rename : ∀ s, MixedVariables n (HistoryIndex cs.length ⊕ (I ⊕ J)) s → V s
    | .vf => Sum.inl
    | .rv => Sum.elim (Sum.inl ∘ Sum.inr) (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)
  exact h.pullback_relabel rename

theorem centerDifferences_test_definable [Finite C]
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (terms : C → SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf) :
    PointTestsDefinable 𝓜 S
      {p : PreparationPoint O (Fin n) I × (Option C × Option C → RV0 O) |
        ∀ i j, p.2 (i,j) = rv O (centerValues O hO power S terms p.1.1 i -
          centerValues O hO power S terms p.1.1 j)} := by
  let rename : ∀ s, MixedVariables n (Option C × Option C) s →
      SumVariables (MixedVariables n I) (RVVariables (Option C × Option C)) s
    | .vf => Sum.inl
    | .rv => Sum.inr
  exact (center_differences_definable O hO power S minusOne hm F hF terms).pullback_relabel rename

end GeneralizedEuler.Section5
