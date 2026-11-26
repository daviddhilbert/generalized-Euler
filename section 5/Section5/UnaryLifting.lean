module

public import Section5.UnaryGradedObjects

/-! The graded RV lift of a unary definable set with finite RV fibers. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

instance historyIndexFintype : (n : ℕ) → Fintype (HistoryIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := historyIndexFintype n
    exact inferInstanceAs (Fintype (HistoryIndex n ⊕ Unit))

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Pack the history and original RV coordinates into one finite tuple. -/
def packUnary {m : ℕ} {cs : List (S.carrier .vf)}
    (idx : Fin m ≃ (HistoryIndex cs.length ⊕ I))
    (p : (K × PreparationLabels O (RV0 O) cs.length) × (I → RV0 O)) :
      K × (Fin m → RV0 O) :=
  (p.1.1, Sum.elim (encodeHistory O cs.length p.1.2) p.2 ∘ idx)

theorem packUnary_injective {m : ℕ} {cs : List (S.carrier .vf)}
    (idx : Fin m ≃ (HistoryIndex cs.length ⊕ I)) :
    Function.Injective (packUnary O hO power S idx) := by
  rintro ⟨⟨x, a⟩, ξ⟩ ⟨⟨y, b⟩, η⟩ he
  have hxy : x = y := congrArg Prod.fst he
  have htags := congrArg Prod.snd he
  have h (i : HistoryIndex cs.length ⊕ I) :
      Sum.elim (encodeHistory O cs.length a) ξ i =
        Sum.elim (encodeHistory O cs.length b) η i := by
    have hi := congrFun htags (idx.symm i)
    change Sum.elim (encodeHistory O cs.length a) ξ (idx (idx.symm i)) =
      Sum.elim (encodeHistory O cs.length b) η (idx (idx.symm i)) at hi
    rw [idx.apply_symm_apply] at hi
    exact hi
  have hab : a = b := by
    have hhistory : encodeHistory O cs.length a = encodeHistory O cs.length b :=
      funext (fun j => h (.inl j))
    simpa only [decode_encode_history] using congrArg (decodeHistory O cs.length) hhistory
  exact Prod.ext (Prod.ext hxy hab) (funext fun j => h (.inr j))

theorem image_prepared_eq_lift {m : ℕ} (cs : List (S.carrier .vf))
    (idx : Fin m ≃ (HistoryIndex cs.length ⊕ I))
    (A : Set (K × (I → RV0 O)))
    (hconst : let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∀ x y ξ, P.label x = P.label y → ((x, ξ) ∈ A ↔ (y, ξ) ∈ A)) :
    let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
    (fun p : K × (I → RV0 O) => packUnary O hO power S idx (P.map p.1, p.2)) '' A =
      {p | p.2 ∘ idx.symm ∈ preparedLabels O hO power S A cs ∧
        rv O p.1 = p.2 (idx.symm (.inl (lastIndex cs.length)))} := by
  intro P
  apply Set.ext
  rintro ⟨y, t⟩
  let labels := t ∘ idx.symm
  let old := decodeHistory O cs.length (labels ∘ Sum.inl)
  let ξ := labels ∘ Sum.inr
  have hlead := lead_decode_history O Subtype.val cs (labels ∘ Sum.inl)
  change P.lead old = labels (.inl (lastIndex cs.length)) at hlead
  change (∃ p ∈ A, packUnary O hO power S idx (P.map p.1, p.2) = (y, t)) ↔
    (∃ x, (x, ξ) ∈ A ∧ P.label x = old) ∧ rv O y = labels (.inl (lastIndex cs.length))
  rw [← hlead]
  constructor
  · rintro ⟨⟨x, ξ'⟩, hx, he⟩
    have he₁ : (P.map x).1 = y := congrArg Prod.fst he
    have he₂ : Sum.elim (encodeHistory O cs.length (P.label x)) ξ' ∘ idx = t :=
      congrArg Prod.snd he
    have he₃ : Sum.elim (encodeHistory O cs.length (P.label x)) ξ' = labels := by
      funext i
      have hi := congrFun he₂ (idx.symm i)
      simpa only [labels, Function.comp_apply, idx.apply_symm_apply] using hi
    have ht : P.label x = old := by
      have history : encodeHistory O cs.length (P.label x) = labels ∘ Sum.inl :=
        funext fun i => congrFun he₃ (.inl i)
      rw [← decode_encode_history O cs.length (P.label x), history]
    have hξ : ξ' = ξ := funext fun i => congrFun he₃ (.inr i)
    exact ⟨⟨x, hξ ▸ hx, ht⟩, he₁ ▸ ht ▸ P.leading x⟩
  · rintro ⟨⟨x, hx, hxt⟩, hy⟩
    obtain ⟨⟨w, ρ⟩, hw, hmap⟩ : ((y, old), ξ) ∈
        (fun p : K × (I → RV0 O) => (P.map p.1, p.2)) '' A := by
      rw [P.image_restriction A hconst]
      exact ⟨hy, x, hx, hxt⟩
    refine ⟨(w, ρ), hw, ?_⟩
    change packUnary O hO power S idx (P.map w, ρ) = (y, t)
    change (P.map w, ρ) = ((y, old), ξ) at hmap
    rw [hmap]
    refine Prod.ext ?_ ?_
    · rfl
    funext j
    change Sum.elim (encodeHistory O cs.length old) ξ (idx j) = t j
    have h := encode_decode_history O cs.length (labels ∘ Sum.inl)
    change encodeHistory O cs.length old = labels ∘ Sum.inl at h
    rw [h]
    have hsum : Sum.elim (labels ∘ Sum.inl) ξ = labels := by
      funext i
      cases i <;> rfl
    rw [hsum]
    exact congrArg t (idx.symm_apply_apply j)

set_option linter.style.haveILetI false in
/-- Corollary 5.8 for one field coordinate. The prepared image is the
union of the lifts of actual degree-zero and degree-one RV objects.
The degree-zero lift is padded by the single field value zero. -/
theorem unary_lift_presentation [Finite I]
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier I)
      (CenterTestAssignments S.carrier I))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : Set (K × (I → RV0 O)))
    (hA : SortedDefinableOver 𝓜 S.carrier {a : ∀ s, MixedVariables 1 I s → CanonicalSort O s |
      (a .vf 0, a .rv) ∈ A})
    (hfib : ∀ x, {ξ | (x, ξ) ∈ A}.Finite) :
    ∃ cs : List (S.carrier .vf), ∃ m, ∃ idx : Fin m ≃ (HistoryIndex cs.length ⊕ I),
      let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
      ∃ U₀ : RVObject 𝓜 S 0, ∃ U₁ : RVObject 𝓜 S 1,
      ∃ r₀ : Fin m ≃ Fin U₀.arity, ∃ r₁ : Fin m ≃ Fin U₁.arity,
        Function.Injective (fun p : K × (I → RV0 O) => packUnary O hO power S idx (P.map p.1, p.2)) ∧
        {p | ∃ x ∈ A, packUnary O hO power S idx (P.map x.1, x.2) = p} =
          {p : K × (Fin m → RV0 O) | p.1 = 0 ∧ ∃ t : U₀.carrier, t.val ∘ r₀ = p.2} ∪
          {p : K × (Fin m → RV0 O) | ∃ t : U₁.carrier, t.val ∘ r₁ = p.2 ∧
            rv O p.1 = U₁.label t 0} := by
  classical
  letI := Fintype.ofFinite I
  obtain ⟨cs, hgraph, hinj, hconst, _⟩ :=
    unary_deformation O hO power S minusOne hm F hF sat immediate A hA
  let m := Fintype.card (HistoryIndex cs.length ⊕ I)
  let idx : Fin m ≃ (HistoryIndex cs.length ⊕ I) :=
    (Fintype.equivFin (HistoryIndex cs.length ⊕ I)).symm
  let i := idx.symm (Sum.inl (lastIndex cs.length))
  let D : Set (Fin m → RV0 O) := {t | t ∘ idx.symm ∈ preparedLabels O hO power S A cs}
  have hD : isRVSet 𝓜 S D :=
    isRVSet_precomp idx.symm (preparedLabels_definable O hO power S A cs hA hgraph)
  have hfin (v : RV0 O) : {t ∈ D | t i = v}.Finite := by
    have h := preparedLabels_finite_fibers O hO power S A cs hfib hconst v
    have hinj : Function.Injective (fun t : Fin m → RV0 O => t ∘ idx.symm) := by
      intro x y he
      funext j
      have ej := congrFun he (idx j)
      simpa only [Function.comp_apply, idx.symm_apply_apply] using ej
    exact h.preimage hinj.injOn
  refine ⟨cs, m, idx, unaryDegreeZero O hO power S D i hD hfin,
    unaryDegreeOne O hO power S D i hD hfin, Equiv.refl _, Equiv.refl _, (packUnary_injective O hO power S idx).comp hinj, ?_⟩
  let P := (UnaryPreparation.regularize (O := O)).prepare Subtype.val cs
  change (fun p : K × (I → RV0 O) => packUnary O hO power S idx (P.map p.1, p.2)) '' A = _
  rw [image_prepared_eq_lift O hO power S cs idx A hconst]
  ext p
  change (p.2 ∈ D ∧ rv O p.1 = p.2 i) ↔
    (p.1 = 0 ∧ ∃ t : {t ∈ D | t i = 0}, t.val = p.2) ∨
    (∃ t : {t ∈ D | t i ≠ 0}, t.val = p.2 ∧ rv O p.1 = t.val i)
  constructor
  · rintro ⟨hp, he⟩
    by_cases hzero : p.2 i = 0
    · exact Or.inl ⟨(rv_eq_zero_iff O).1 (he.trans hzero), ⟨p.2, hp, hzero⟩, rfl⟩
    · exact Or.inr ⟨⟨p.2, hp, hzero⟩, rfl, he⟩
  · rintro (⟨hy, ⟨t, ht⟩⟩ | ⟨t, ht, hy⟩)
    · exact ⟨ht ▸ t.property.1, ((rv_eq_zero_iff O).2 hy).trans ((ht ▸ t.property.2).symm)⟩
    · exact ⟨ht ▸ t.property.1, ht ▸ hy⟩

end GeneralizedEuler.Section5
