module

public import Section5.PreparedUnaryRVIndex
public import Section5.RelativeElementaryRows

/-! The tags and structure maps of a finite collection of elementary
schemes are constant on the histories of one unary preparation. -/

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
local notation "X" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty

theorem prepare_relative_elementary_schemes {J : Type*} [Finite J]
    (deg : J → ℕ) (W : ∀ j, RelativeElementaryScheme 𝓜 S P (deg j))
    (bases : J → Set (SortedAssignment X P))
    (defBases : ∀ j, SortedDefinableOver 𝓜 S.carrier (bases j))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (satBase : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier Empty)
      (CenterTestAssignments S.carrier Empty))
    (satTags : ∀ j, RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier (Fin (W j).arity))
      (CenterTestAssignments S.carrier (Fin (W j).arity)))
    (satGraph : ∀ j, RealizesFinitelySatisfiableTypes 𝓜
      (CenterTestVariables S.carrier (Fin (W j).arity ⊕ Fin (deg j+1)))
      (CenterTestAssignments S.carrier (Fin (W j).arity ⊕ Fin (deg j+1))))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t) :
    ∃ cs : List (S.carrier .vf),
      let T := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ (j : J) (p p' : SortedAssignment X P), T.label (p .vf 0) = T.label (p' .vf 0) →
        (p ∈ bases j ↔ p' ∈ bases j) ∧
        (∀ a, appendAssignments p a ∈ (W j).tags ↔ appendAssignments p' a ∈ (W j).tags) ∧
        (∀ a b, appendAssignments (appendAssignments p a) b ∈ (W j).graph ↔
          appendAssignments (appendAssignments p' a) b ∈ (W j).graph) := by
  let U (j : J) := RVVariables (Fin (W j).arity)
  let V (j : J) := RVVariables (Fin (deg j+1))
  let I : J ⊕ (J ⊕ J) → Type :=
    Sum.elim (fun _ => Empty) (Sum.elim (fun j => Fin (W j).arity) (fun j => Fin (W j).arity ⊕ Fin (deg j+1)))
  let rename (j : J) : (s : TCsort) → SumVariables (SumVariables P (U j)) (V j) s →
      SumVariables P (RVVariables (I (.inr (.inr j)))) s
    | .vf => Sum.elim (Sum.elim Sum.inl PEmpty.elim) PEmpty.elim
    | .rv => Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  let D : ∀ j, Set (SortedAssignment X (SumVariables P (RVVariables (I j))))
    | .inl j => {a | (fun s => a s ∘ Sum.inl) ∈ bases j}
    | .inr (.inl j) => (W j).tags
    | .inr (.inr j) => {a | (fun s => a s ∘ rename j s) ∈ (W j).graph}
  have defD (j : J ⊕ (J ⊕ J)) : SortedDefinableOver 𝓜 S.carrier (D j) := by
    rcases j with j | (j | j)
    · exact (defBases j).pullback_relabel (fun _ => Sum.inl)
    · exact (W j).tagsDefinable
    · exact (W j).graphDefinable.pullback_relabel (rename j)
  have sat (j : J ⊕ (J ⊕ J)) : RealizesFinitelySatisfiableTypes 𝓜
      (CenterTestVariables S.carrier (I j)) (CenterTestAssignments S.carrier (I j)) := by
    rcases j with j | (j | j)
    · exact satBase
    · exact satTags j
    · exact satGraph j
  obtain ⟨cs,_,same,_⟩ := unary_preparation_of_witness_schemes O hO power S I F minusOne hm hF sat immediate D defD
  refine ⟨cs,?_⟩
  intro T j p p' eq
  let q : SortedAssignment X (RVVariables (HistoryIndex cs.length))
    | .vf => PEmpty.elim
    | .rv => encodeHistory O cs.length (T.label (p .vf 0))
  let R (p : SortedAssignment X P) (q : SortedAssignment X (RVVariables (HistoryIndex cs.length))) :=
    T.label (p .vf 0) = decodeHistory O cs.length (q .rv)
  have h : R p q := (decode_encode_history O cs.length _).symm
  have h' : R p' q := eq.symm.trans h
  have const (i : J ⊕ (J ⊕ J)) (a : SortedAssignment X (RVVariables (I i))) :
      appendAssignments p a ∈ D i ↔ appendAssignments p' a ∈ D i :=
    (same i p q h a).symm.trans (same i p' q h' a)
  let noneRV : SortedAssignment X (RVVariables (I (.inl j)))
    | .vf => PEmpty.elim
    | .rv => Empty.elim
  refine ⟨const (.inl j) noneRV,const (.inr (.inl j)),?_⟩
  intro a b
  let r : SortedAssignment X (RVVariables (I (.inr (.inr j)))) := RVObject.labelGraphTuple (a .rv) (b .rv)
  have pack (x : SortedAssignment X P) :
      (fun s => appendAssignments x r s ∘ rename j s) = appendAssignments (appendAssignments x a) b := by
    funext s i
    rcases i with (i | i) | i
    · cases s <;> rfl
    · cases s
      · exact i.elim
      · rfl
    · cases s
      · exact i.elim
      · rfl
  have test := const (.inr (.inr j)) r
  change (fun s => appendAssignments p r s ∘ rename j s) ∈ (W j).graph ↔
    (fun s => appendAssignments p' r s ∘ rename j s) ∈ (W j).graph at test
  simpa only [pack] using test

end GeneralizedEuler.Section5
