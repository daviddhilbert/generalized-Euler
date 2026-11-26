module

public import Section5.CenterDifferences
public import Section5.PreparationGraph
public import Section5.VerticalImages

/-! Fixed-base input for the successor step of field-arity induction. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language UnaryPreparation

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n : ℕ} {I : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

set_option linter.style.haveILetI false in
/-- A definable family in one distinguished field coordinate admits a
single finite list of center terms in the remaining field coordinates.
Both the resulting coordinate map and the tuple to prepare on the tail
are definable over the original base. -/
theorem uniform_vertical_preparation
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n I))
      (BaseAssignments S.carrier (VerticalPairVariables n I)))
    (immediate : ∀ (b : Fin n → K) (x y : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S b)
      (∀ c : B.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set (K × ((Fin n → K) × (I → RV0 O))))
    (hA : SortedDefinableOver 𝓜 S.carrier {a : ∀ s, VerticalVariables n I s → CanonicalSort O s |
      (a .vf (.inl ()), a .vf ∘ Sum.inr, a .rv) ∈ A}) :
    ∃ (m : ℕ) (terms : Fin m → SortedTerm L E (WithBase S.carrier (MixedVariables n Empty)) .vf),
      let cs := List.ofFn (id : Fin m → Fin m)
      let center := centerValues O hO power S terms
      (∀ b x y ξ, (centerPreparation (O := O) (center b) cs).label x =
          (centerPreparation (O := O) (center b) cs).label y →
        ((x, b, ξ) ∈ A ↔ (y, b, ξ) ∈ A)) ∧
      SortedDefinableOver 𝓜 S.carrier
        {v : ∀ s, HistoryGraphVariables n cs.length s → CanonicalSort O s |
          (centerPreparation (O := O) (center (v .vf ∘ Sum.inr)) cs).map (v .vf (.inl 0)) =
            (v .vf (.inl 1), decodeHistory O cs.length (v .rv))} ∧
      SortedDefinableOver 𝓜 S.carrier
        {v : ∀ s, MixedVariables n (Option (Fin m) × Option (Fin m)) s → CanonicalSort O s |
          ∀ i j, v .rv (i,j) = rv O (center (v .vf) i - center (v .vf) j)} := by
  classical
  obtain ⟨C, hC⟩ := finite_vertical_centers O hO power S minusOne hm F hF sat immediate A hA
  let m := Fintype.card C
  let e : Fin m ≃ C := (Fintype.equivFin C).symm
  let terms (i : Fin m) := (e i).val
  let cs := List.ofFn (id : Fin m → Fin m)
  refine ⟨m, terms, ?_, ?_, center_differences_definable O hO power S minusOne hm F hF terms⟩
  · intro b x y ξ ht
    have he := ((regularize (O := O)).prepare_decides
      (centerValues O hO power S terms b ∘ some) cs ht).2
    apply hC b x y ξ
    intro t ht'
    let i := e.symm ⟨t, ht'⟩
    have hi : i ∈ cs := by
      change i ∈ List.ofFn (id : Fin m → Fin m)
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    have eq : terms i = t := congrArg Subtype.val (e.apply_symm_apply ⟨t, ht'⟩)
    have hv := he i hi
    change rv O (x - (terms i).realize 𝓜 (centerAssignment O hO power S b)) =
      rv O (y - (terms i).realize 𝓜 (centerAssignment O hO power S b)) at hv
    simpa only [eq] using hv
  · exact preparationGraph_of_terms O hO power S F minusOne hm hF terms cs

end GeneralizedEuler.Section5
