module

public import Section5.UniformVerticalPreparation

/-! Definability of the relation after replacing the head field
coordinate by the full history of a vertical preparation. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language UnaryPreparation

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n : ℕ} {I J : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- The relation after vertical preparation. The prepared head field
coordinate can be dropped because the original graph is constant on
each full head history. -/
theorem descended_vertical_graph_definable
    (A : Set (K × ((Fin n → K) × (I → RV0 O))))
    (hA : SortedDefinableOver 𝓜 S.carrier {a : ∀ s, VerticalVariables n I s → CanonicalSort O s |
      (a .vf (.inl ()), a .vf ∘ Sum.inr, a .rv) ∈ A})
    (center : (Fin n → K) → Option J → K) (cs : List J)
    (hmap : SortedDefinableOver 𝓜 S.carrier
      {v : ∀ s, HistoryGraphVariables n cs.length s → CanonicalSort O s |
        (centerPreparation (O := O) (center (v .vf ∘ Sum.inr)) cs).map (v .vf (.inl 0)) =
          (v .vf (.inl 1), decodeHistory O cs.length (v .rv))}) :
    SortedDefinableOver 𝓜 S.carrier
      {v : ∀ s, MixedVariables n (HistoryIndex cs.length ⊕ I) s → CanonicalSort O s |
        ∃ x, (x, v .vf, v .rv ∘ Sum.inr) ∈ A ∧
          (centerPreparation (O := O) (center (v .vf)) cs).label x =
            decodeHistory O cs.length (v .rv ∘ Sum.inl)} := by
  let V := MixedVariables n (HistoryIndex cs.length ⊕ I)
  let VY := AddSortedVar V .vf
  let VXY := AddSortedVar VY .vf
  let renameGraph : ∀ s, HistoryGraphVariables n cs.length s → VXY s
    | .vf => Sum.elim (Fin.cases (.inr ⟨rfl⟩) (fun _ => .inl (.inr ⟨rfl⟩))) (fun j => .inl (.inl j))
    | .rv => fun i => .inl (.inl (.inl i))
  let renameSet : ∀ s, VerticalVariables n I s → VXY s
    | .vf => Sum.elim (fun _ => .inr ⟨rfl⟩) (fun j => .inl (.inl j))
    | .rv => fun i => .inl (.inl (.inr i))
  have hrestrict := (hA.pullback_relabel renameSet).inter (hmap.pullback_relabel renameGraph)
  have proj := (hrestrict.project_one .vf).project_one .vf
  convert proj using 1
  ext v
  let P := centerPreparation (O := O) (center (v .vf)) cs
  let t := decodeHistory O cs.length (v .rv ∘ Sum.inl)
  change (∃ x, (x, v .vf, v .rv ∘ Sum.inr) ∈ A ∧ P.label x = t) ↔
    ∃ y x, (x, v .vf, v .rv ∘ Sum.inr) ∈ A ∧ P.map x = (y, t)
  constructor
  · rintro ⟨x, hx, ht⟩
    exact ⟨(P.map x).1, x, hx, Prod.ext rfl ht⟩
  · rintro ⟨_, x, hx, he⟩
    exact ⟨x, hx, congrArg Prod.snd he⟩

end GeneralizedEuler.Section5
