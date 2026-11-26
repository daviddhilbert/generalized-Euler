module

public import Section5.RVPatternObjects

/-! A mixed prepared object is the union of the padded lifts of its
graded RV objects. The support records the nonzero field leading terms. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {n a : ℕ} {I J : Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable {G : PointTests O n I J} (P : PreparedMap (canonicalStructure (L := L) O hO power) S G)

theorem PreparedMap.packed_labels_finite
    (hf : ∀ a, {t | (a,t) ∈ testDomain G}.Finite) (s : Fin n → RV0 O) :
    {t | Sum.elim s t ∈ packPullbackLabel '' (P.map '' testDomain G)}.Finite := by
  apply (P.domain_labels_finite_over_lead hf s).subset
  rintro t ⟨b,hb,he⟩
  have hh : preparationLabel b = (s,t) :=
    Prod.ext (funext fun i => congrFun he (.inl i)) (funext fun i => congrFun he (.inr i))
  exact ⟨b,hb,hh⟩

/-- Append all field leading terms to the RV tuple and pack it.
This regularization keeps all original RV data. -/
@[expose] def packPrepared (idx : Fin a ≃ Fin n ⊕ P.tags)
    (p : PreparationPoint O (Fin n) P.tags) : PreparationPoint O (Fin n) (Fin a) :=
  (p.1, packPullbackLabel p ∘ idx)

theorem packPrepared_injective (idx : Fin a ≃ Fin n ⊕ P.tags) :
    Function.Injective (packPrepared O hO power S P idx) := by
  intro b c he
  obtain ⟨hVF,hRV⟩ := Prod.mk.inj he
  apply Prod.ext hVF
  funext i
  have h := congrFun hRV (idx.symm (.inr i))
  simpa only [Function.comp_apply, idx.apply_symm_apply, packPullbackLabel, Sum.elim_inr] using h

theorem packPrepared_definable (idx : Fin a ≃ Fin n ⊕ P.tags) :
    PointMapDefinable 𝓜 S (packPrepared O hO power S P idx) := by
  let := P.finiteTags
  let V := SumVariables (MixedVariables n P.tags) (MixedVariables n (Fin a))
  let rename : ∀ s, SumVariables (MixedVariables n P.tags) (RVVariables (Fin n ⊕ P.tags)) s → V s
    | .vf => Sum.elim Sum.inl PEmpty.elim
    | .rv => Sum.map id idx.symm
  have hpack := packPullbackLabel_definable hO power S (n := n) (I := P.tags)
  unfold DefinableRelation at hpack
  have hf := SortedDefinableOver.iInter (fun i : Fin n =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := V) .vf (.inl i) (.inr i))
  unfold PointMapDefinable DefinableRelation
  convert hf.inter (hpack.pullback_relabel rename) using 1
  ext v
  let p : PreparationPoint O (Fin n) P.tags := (v .vf ∘ Sum.inl, v .rv ∘ Sum.inl)
  change (p.1, packPullbackLabel p ∘ idx) = (v .vf ∘ Sum.inr, v .rv ∘ Sum.inr) ↔
    (v ∈ ⋂ i : Fin n, {x | x .vf (.inl i) = x .vf (.inr i)}) ∧
      packPullbackLabel p = (v .rv ∘ Sum.inr) ∘ idx.symm
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro he
    obtain ⟨hh, ht⟩ := Prod.mk.inj he
    refine ⟨fun i => congrFun hh i, ?_⟩
    funext j
    have h := congrFun ht (idx.symm j)
    simpa only [Function.comp_apply, idx.apply_symm_apply] using h
  · rintro ⟨hf',he⟩
    refine Prod.ext (funext hf') ?_
    rw [he]
    funext i
    exact congrArg (v .rv ∘ Sum.inr) (idx.symm_apply_apply i)

theorem packed_preparation_special (idx : Fin a ≃ Fin n ⊕ P.tags)
    (h : SpecialChain O (Fin n) Set.univ P.map) :
    SpecialChain O (Fin n) (testDomain G) (packPrepared O hO power S P idx ∘ P.map) := by
  have hc : ∀ b ∈ P.map '' testDomain G, ∀ c ∈ P.map '' testDomain G,
      preparationLabel (regularizeBy O idx b) = preparationLabel (regularizeBy O idx c) →
      b.2 = c.2 := by
    intro b _ c _ he
    have he' := congrArg Prod.snd he
    funext i
    have h := congrFun he' (idx.symm (.inr i))
    change packPullbackLabel b (idx (idx.symm (.inr i))) =
      packPullbackLabel c (idx (idx.symm (.inr i))) at h
    rwa [idx.apply_symm_apply] at h
  exact .append (P.on_testDomain_special h) (.regularization _ idx hc)

variable (idx : Fin a ≃ Fin n ⊕ P.tags)
  (degree : Set (Fin n) → ℕ) (selected : ∀ support, Fin (degree support) ≃ support)

private abbrev RVLabels :=
  packPullbackLabel '' (P.map '' testDomain G)

/-- Each pattern consists of an ordinary RV object in its active degree.
Its lift keeps the original field arity, padding the omitted field
coordinates by zero. -/
theorem prepared_lift_by_pattern [Finite I] [Finite J]
    (hG : PointTestsDefinable 𝓜 S G)
    (hf : ∀ a, {t | (a,t) ∈ testDomain G}.Finite) :
    ∃ U : (support : Set (Fin n)) → RVObject 𝓜 S (degree support),
      ∃ pack : ∀ support, Fin a ≃ Fin (U support).arity,
      packPrepared O hO power S P idx '' (P.map '' testDomain G) =
        {p | ∃ (support : Set (Fin n)) (t : (U support).carrier),
            t.val ∘ pack support = p.2 ∧
            (∀ j, rv O (p.1 (selected support j).val) = (U support).label t j) ∧
            (∀ i ∉ support, p.1 i = 0)} := by
  classical
  let D := RVLabels (P := P)
  have hd : isRVSet 𝓜 S D := prepared_labels_definable hO power S P hG
  have hf' := PreparedMap.packed_labels_finite O hO power S P hf
  let U (support : Set (Fin n)) := patternRVObject O hO power S D idx support (selected support) hd hf'
  refine ⟨U, fun _ => Equiv.refl _, ?_⟩
  ext b
  constructor
  · rintro ⟨p,hp,rfl⟩
    let support : Set (Fin n) := {i | rv O (p.1 i) ≠ 0}
    let t := packPullbackLabel p ∘ idx
    have ht : t ∈ patternLabels O D idx support := by
      constructor
      · have ht' : t ∘ idx.symm = packPullbackLabel p := by
          funext i
          exact congrArg (packPullbackLabel p) (idx.apply_symm_apply i)
        rw [ht']
        exact ⟨p,hp,rfl⟩
      · intro i
        change packPullbackLabel p (idx (idx.symm (.inl i))) ≠ 0 ↔ _
        rw [idx.apply_symm_apply]
        rfl
    refine ⟨support,⟨t,ht⟩,rfl,?_,?_⟩
    · intro j
      change rv O (p.1 (selected support j).val) =
        packPullbackLabel p (idx (idx.symm (.inl (selected support j).val)))
      rw [idx.apply_symm_apply]
      rfl
    · intro i hi
      exact (rv_eq_zero_iff O).1 (Classical.byContradiction hi)
  · rintro ⟨support,t,he,hactive,hzero⟩
    have htags : t.val = b.2 := he
    have ht : t.val ∈ patternLabels O D idx support := t.property
    let p : PreparationPoint O (Fin n) P.tags :=
      (b.1,t.val ∘ idx.symm ∘ Sum.inr)
    have hl : packPullbackLabel p = t.val ∘ idx.symm := by
      funext i
      cases i with
      | inr _ => rfl
      | inl i =>
        change rv O (b.1 i) = t.val (idx.symm (.inl i))
        by_cases hi : i ∈ support
        · let j := (selected support).symm ⟨i,hi⟩
          have hj := (selected support).apply_symm_apply ⟨i,hi⟩
          have hv := hactive j
          change rv O (b.1 (selected support j).val) =
            t.val (idx.symm (.inl (selected support j).val)) at hv
          rwa [hj] at hv
        · have hz : t.val (idx.symm (.inl i)) = 0 :=
            Classical.byContradiction (fun h => hi ((ht.2 i).1 h))
          rw [hzero i hi, hz, map_zero]
    have hp : p ∈ P.map '' testDomain G := by
      have hmem : packPullbackLabel p ∈ D := hl.symm ▸ ht.1
      obtain ⟨q,hq,hq'⟩ := hmem
      have hVF : rv O ∘ q.1 = rv O ∘ p.1 := funext fun i => congrFun hq' (.inl i)
      have hRV : q.2 = p.2 := funext fun i => congrFun hq' (.inr i)
      exact (P.domain_image_whole q p (Prod.ext hVF hRV)).1 hq
    refine ⟨p,hp,Prod.ext rfl ?_⟩
    change packPullbackLabel p ∘ idx = b.2
    rw [hl, ← htags]
    funext j
    exact congrArg t.val (idx.symm_apply_apply j)

end GeneralizedEuler.Section5
