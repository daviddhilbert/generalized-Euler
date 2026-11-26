module

public import Section5.SpecialSuccessor
public import Section5.CenterBase

/-! Definable preparation of mixed graphs in every finite field arity. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language UnaryPreparation

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1100000 in
/-- One fixed-base definable injection prepares all RV-output tests in
any finite field arity. The target is a pullback and every original RV
coordinate is kept in a specified slot. The proof is by field arity. -/
theorem preparedMap_of_definable
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ n (I : Type), Finite I →
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n I))
        (BaseAssignments S.carrier (VerticalPairVariables n I)))
    (immediate : ∀ n (b : Fin n → K) (x y : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S b)
      (∀ c : B.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    {n : ℕ} {I J : Type} [Finite I] [Finite J]
    (G : PointTests O n I J) (hG : PointTestsDefinable 𝓜 S G) :
    ∃ P : PreparedMap 𝓜 S G, SpecialChain O (Fin n) Set.univ P.map := by
  induction n generalizing I J with
  | zero => exact ⟨PreparedMap.zero G, .id Set.univ⟩
  | succ n ih =>
    obtain ⟨m, terms, ht, hmap, _⟩ := uniform_vertical_preparation O hO power S minusOne hm F hF
      (sat n (I ⊕ J) inferInstance) (immediate n) (verticalForm O G)
      (verticalForm_definable O hO power S hG)
    let cs := List.ofFn (id : Fin m → Fin m)
    let center := centerValues O hO power S terms
    let P (b : Fin n → K) := centerPreparation (O := O) (center b) cs
    have hhead : PointMapDefinable 𝓜 S (headMap (I := I) P) := headMap_definable P hmap
    have hdiff := centerDifferences_test_definable (I := I) O hO power S minusOne hm F hF terms
    obtain ⟨first, firstSpecial⟩ := ih _ hdiff
    letI := first.finiteTags
    have hdG := descendedTest_definable O hO power S hG center cs hmap
    have hdU := descendedTest_definable O hO power S
      (PointTestsDefinable.univ (M := 𝓜) (S := S) (n := n+1) (I := I) (J := J)) center cs hmap
    have htailG := transportedTailTest_definable P first.map hdG first.definable
    have htailU := transportedTailTest_definable P first.map hdU first.definable
    have hflag := flagTests_definable hO power S htailU htailG
    obtain ⟨last, lastSpecial⟩ := ih _ hflag
    have hLead (b : Fin n → K) (t : PreparationLabels O (RV0 O) cs.length) :
        (P b).lead t = encodeHistory O cs.length t (lastIndex cs.length) := by
      have h := lead_decode_history O (center b ∘ some) cs (encodeHistory O cs.length t)
      rw [decode_encode_history] at h
      exact h
    have hconst (b : Fin n → K) (x y : K) (ξ : I → RV0 O) (s : J → RV0 O)
        (he : (P b).label x = (P b).label y) :
        (((Fin.cons x b, ξ),s) ∈ G ↔ ((Fin.cons y b, ξ),s) ∈ G) :=
      ht b x y (Sum.elim ξ s) he
    refine ⟨PreparedMap.successor P first.map G first.definable first.injective
      first.oldIndex first.oldAux hhead (lastIndex cs.length) hLead hconst last, ?_⟩
    exact specialSuccessor center first cs (fun _ => rfl) firstSpecial last.map lastSpecial

end GeneralizedEuler.Section5
