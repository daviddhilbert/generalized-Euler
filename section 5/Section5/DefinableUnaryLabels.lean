module

public import Section5.UnaryDeformation
public import Section5.UnaryLiftObjects
public import Section4.FiniteScissors

/-! The RV presentation of a unary pullback over the same base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type}

local notation "M" => canonicalStructure (L := L) O hO power

variable (A : Set (K × (I → RV0 O))) (cs : List (S.carrier .vf))

/-- The packed RV label consists of the full preparation history and
the original auxiliary tuple. -/
@[expose] def preparedLabels : Set (HistoryIndex cs.length ⊕ I → RV0 O) :=
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  {t | ∃ x, (x, t ∘ Sum.inr) ∈ A ∧ P.label x = decodeHistory O cs.length (t ∘ Sum.inl)}

/-- Project the input and output field coordinates from the graph of the
preparation restricted to the original set. -/
theorem preparedLabels_definable
    (hA : SortedDefinableOver M S.carrier {a : ∀ s, MixedVariables 1 I s → CanonicalSort O s |
      (a .vf 0, a .rv) ∈ A})
    (hmap : SortedDefinableOver M S.carrier
      {v : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → CanonicalSort O s |
        ((UnaryPreparation.regularize (O := O)).prepare Subtype.val cs).map (v .vf 0) =
          (v .vf 1, decodeHistory O cs.length (v .rv))}) :
    isRVSet M S (preparedLabels O hO power S A cs) := by
  let V := RVVariables (HistoryIndex cs.length ⊕ I)
  let VY := AddSortedVar V .vf
  let VXY := AddSortedVar VY .vf
  let renamedGraph : ∀ s, MixedVariables 2 (HistoryIndex cs.length) s → VXY s
    | .vf => Fin.cases (.inr ⟨rfl⟩) (fun _ => .inl (.inr ⟨rfl⟩))
    | .rv => fun i => .inl (.inl (.inl i))
  let renamedSet : ∀ s, MixedVariables 1 I s → VXY s
    | .vf => fun _ => .inr ⟨rfl⟩
    | .rv => fun i => .inl (.inl (.inr i))
  have hrestrict := (hA.pullback_relabel renamedSet).inter (hmap.pullback_relabel renamedGraph)
  have proj := (hrestrict.project_one .vf).project_one .vf
  unfold isRVSet
  convert proj using 1
  ext v
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  change (∃ x, (x, v .rv ∘ Sum.inr) ∈ A ∧
      P.label x = decodeHistory O cs.length (v .rv ∘ Sum.inl)) ↔
    ∃ y x, (x, v .rv ∘ Sum.inr) ∈ A ∧
      P.map x = (y, decodeHistory O cs.length (v .rv ∘ Sum.inl))
  constructor
  · rintro ⟨x, hx, ht⟩
    exact ⟨(P.map x).1, x, hx, Prod.ext rfl ht⟩
  · rintro ⟨_, x, hx, he⟩
    exact ⟨x, hx, congrArg Prod.snd he⟩

/-- Finite fibers of the field object give finite fibers for the retained
leading-term coordinate on the packed RV labels. -/
theorem preparedLabels_finite_fibers
    (hf : ∀ x, {ξ | (x, ξ) ∈ A}.Finite)
    (hconst : let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ x y ξ, P.label x = P.label y → ((x, ξ) ∈ A ↔ (y, ξ) ∈ A))
    (s : RV0 O) :
    {t ∈ preparedLabels O hO power S A cs | t (.inl (lastIndex cs.length)) = s}.Finite := by
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  let pack (p : PreparationLabels O (RV0 O) cs.length × (I → RV0 O)) :
      HistoryIndex cs.length ⊕ I → RV0 O :=
    Sum.elim (encodeHistory O cs.length p.1) p.2
  have hfinite := P.finite_rv_labels A hf
    (UnaryPreparation.finite_prepared_offsets (O := O) Subtype.val cs) hconst s
  apply (hfinite.image pack).subset
  rintro t ⟨⟨x, hx, hxt⟩, ht⟩
  refine ⟨(decodeHistory O cs.length (t ∘ Sum.inl), t ∘ Sum.inr), ⟨?_, x, hx, hxt⟩, ?_⟩
  · exact (lead_decode_history O Subtype.val cs _).trans ht
  · funext i
    cases i with
    | inl i => exact congrFun (encode_decode_history O cs.length _) i
    | inr i => rfl

end GeneralizedEuler.Section5
