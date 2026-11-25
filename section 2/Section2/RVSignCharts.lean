module

public import Section2.DefinableAffinePartitions
public import Mathlib.Data.Fintype.Pi

/-! Sign changes preserve the value set and the original definability
base in the affine charts of Lemma 2.29. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder RVValueSection

universe u v w z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)

private def signedRVNeg (x : RV0 O) : RV0 O := rv O (-1) * x

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem signedRVNeg_rv (x : K) : signedRVNeg O (rv O x) = rv O (-x) := by
  rw [signedRVNeg, ← map_mul (rv O), neg_one_mul]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem signedRVNeg_neg (x : RV0 O) : signedRVNeg O (signedRVNeg O x) = x := by
  obtain ⟨y, rfl⟩ := rv_surjective O x
  rw [signedRVNeg_rv, signedRVNeg_rv, neg_neg]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem valueCoordinate_signedRVNeg (x : RV0 O) :
    valueCoordinate (signedRVNeg O x) = valueCoordinate x := by
  obtain ⟨y, rfl⟩ := rv_surjective O x
  rw [signedRVNeg_rv]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [neg_zero]
  apply Units.ext
  rw [coe_valueCoordinate ((rv_eq_zero_iff O).not.mpr (neg_ne_zero.mpr hy)),
    coe_valueCoordinate ((rv_eq_zero_iff O).not.mpr hy), unsignedValue_rv, unsignedValue_rv, O.valuation.map_neg]

variable {I : Type} (sign : I → Bool)

private def changeRVSigns (x : I → RV0 O) (i : I) : RV0 O :=
  if sign i then signedRVNeg O (x i) else x i

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem changeRVSigns_twice (x : I → RV0 O) : changeRVSigns O sign (changeRVSigns O sign x) = x := by
  funext i
  cases h : sign i <;> simp only [changeRVSigns, h, Bool.false_eq_true, ↓reduceIte, signedRVNeg_neg]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem valueCoordinate_changeRVSigns (x : I → RV0 O) (i : I) :
    valueCoordinate (changeRVSigns O sign x i) = valueCoordinate (x i) := by
  cases h : sign i <;>
    simp only [changeRVSigns, h, Bool.false_eq_true, ↓reduceIte, valueCoordinate_signedRVNeg]

/-- One fixed sign pattern of a value pullback. A true component is
negative, so the specified sign changes send the tuple to positive RV. -/
def signedValuePullback (U : Set (I → Additive O.ValueGroupˣ)) : Set (I → RV0 O) :=
  {x | (∀ i, IsPositiveRV O (changeRVSigns O sign x i)) ∧
    (Additive.ofMul ∘ valueCoordinate ∘ x) ∈ U}

/-- A true component records a negative leading term. -/
def rvSignPattern (hO : IsOrderConvex O) (x : I → RV0 O) (i : I) : Bool :=
  letI := rvLinearOrder O hO
  decide (x i < 0)

set_option linter.style.haveILetI false in
private theorem changeRVSigns_positive_iff (hO : IsOrderConvex O) (x : I → RV0 O) (i : I) :
    IsPositiveRV O (changeRVSigns O sign x i) ↔ x i ≠ 0 ∧ sign i = rvSignPattern O hO x i := by
  letI := rvLinearOrder O hO
  obtain ⟨a, ha⟩ := rv_surjective O (x i)
  have hn : rv O a ≠ 0 ↔ a ≠ 0 := (rv_eq_zero_iff O).not
  cases hs : sign i
  · simp only [changeRVSigns, hs, Bool.false_eq_true, ↓reduceIte, rvSignPattern, ← ha,
      isPositiveRV_rv_iff, hn]
    have dec : (false = decide (rv O a < 0)) ↔ 0 ≤ a := by
      rw [eq_comm, decide_eq_false_iff_not, rv_lt_zero_iff O hO, not_lt]
    rw [dec]
    exact ⟨fun h => ⟨h.ne', h.le⟩, fun h => lt_of_le_of_ne h.2 (Ne.symm h.1)⟩
  · simp only [changeRVSigns, hs, ↓reduceIte, rvSignPattern, ← ha, signedRVNeg_rv,
      isPositiveRV_rv_iff, hn, neg_pos]
    have dec : (true = decide (rv O a < 0)) ↔ a < 0 := by
      rw [eq_comm, decide_eq_true_eq, rv_lt_zero_iff O hO]
    rw [dec]
    exact ⟨fun h => ⟨h.ne, h⟩, And.right⟩

/-- The pullback of a value set given separately on the two signs in
each coordinate. -/
def signIndexedValuePullback (hO : IsOrderConvex O) (U : (I → Bool) → Set (I → Additive O.ValueGroupˣ)) :
    Set (I → RV0 O) :=
  {x | (∀ i, x i ≠ 0) ∧ (Additive.ofMul ∘ valueCoordinate ∘ x) ∈ U (rvSignPattern O hO x)}

theorem signIndexedValuePullback_eq_union (hO : IsOrderConvex O)
    (U : (I → Bool) → Set (I → Additive O.ValueGroupˣ)) :
    signIndexedValuePullback O hO U = ⋃ s : I → Bool, signedValuePullback O s (U s) := by
  ext x
  constructor
  · rintro ⟨hn, hu⟩
    exact Set.mem_iUnion.mpr ⟨rvSignPattern O hO x,
      fun i => (changeRVSigns_positive_iff O (rvSignPattern O hO x) hO x i).mpr ⟨hn i, rfl⟩, hu⟩
  · intro hx
    obtain ⟨s, hs, hu⟩ := Set.mem_iUnion.mp hx
    have h i := (changeRVSigns_positive_iff O s hO x i).mp (hs i)
    have he : s = rvSignPattern O hO x := funext fun i => (h i).2
    exact ⟨fun i => (h i).1, he ▸ hu⟩

theorem signedValuePullback_pairwise_disjoint (hO : IsOrderConvex O)
    (U : (I → Bool) → Set (I → Additive O.ValueGroupˣ)) :
    Pairwise (fun s t => Disjoint (signedValuePullback O s (U s)) (signedValuePullback O t (U t))) := by
  intro s t hst
  refine Set.disjoint_left.mpr (fun x hs ht => hst ?_)
  funext i
  exact ((changeRVSigns_positive_iff O s hO x i).mp (hs.1 i)).2.trans
    (((changeRVSigns_positive_iff O t hO x i).mp (ht.1 i)).2.symm)

variable {L : Language.{u, v}} [L.Structure K] [L.Structure (Residue O)]
  {E : Type w} (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (A : ∀ s, Set (CanonicalSort O s))

/-- A fixed sign piece is definably equivalent to its positive
counterpart by multiplication by the named negative unit. -/
theorem signedValuePullback_definablyEquivalent [Finite I] (U : Set (I → Additive O.ValueGroupˣ))
    (hminus : rv O (-1) ∈ A .rv)
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO power) A
      {x : ∀ s, RVVariables I s → CanonicalSort O s | x .rv ∈ signedValuePullback O sign U}) :
    RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) A
      (signedValuePullback O sign U) (positiveValuePullback O U) := by
  let F := changeRVSigns O sign
  have hv (x : I → RV0 O) :
      Additive.ofMul ∘ valueCoordinate ∘ F x = Additive.ofMul ∘ valueCoordinate ∘ x :=
    funext fun i => congrArg Additive.ofMul (valueCoordinate_changeRVSigns O sign x i)
  let e : signedValuePullback O sign U ≃ positiveValuePullback O U :=
    { toFun := fun x => ⟨F x.val, x.property.1, (hv x.val).symm ▸ x.property.2⟩
      invFun := fun y => ⟨F y.val, (changeRVSigns_twice O sign y.val).symm ▸ y.property.1,
        (hv y.val).symm ▸ y.property.2⟩
      left_inv := fun x => Subtype.ext (changeRVSigns_twice O sign x.val)
      right_inv := fun y => Subtype.ext (changeRVSigns_twice O sign y.val) }
  refine ⟨e, ?_⟩
  let M := canonicalStructure (L := L) O hO power
  let Var := RVVariables (I ⊕ I)
  let src : ∀ s, RVVariables I s → Var s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  let Domain : Set (∀ s, Var s → CanonicalSort O s) := {a | a .rv ∘ Sum.inl ∈ signedValuePullback O sign U}
  let Graph (i : I) : Set (∀ s, Var s → CanonicalSort O s) :=
    {a | a .rv (.inr i) = F (a .rv ∘ Sum.inl) i}
  have hDomain : SortedDefinableOver M A Domain := hD.pullback_relabel src
  have hGraph (i : I) : SortedDefinableOver M A (Graph i) := by
    let input : SortedTerm L E (fun s => (A s : Type z) ⊕ Var s) .rv := .var (.inr (.inl i))
    let negOne : SortedTerm L E (fun s => (A s : Type z) ⊕ Var s) .rv := .var (.inl ⟨_, hminus⟩)
    cases hs : sign i
    · have h := SortedDefinableOver.coordinate_eq (M := M) (A := A) (Var := Var)
        .rv (.inr i) (.inl i)
      convert h using 1
      ext a
      change (a .rv (.inr i) = F (a .rv ∘ Sum.inl) i) ↔ a .rv (.inr i) = a .rv (.inl i)
      simp only [F, changeRVSigns, hs, Bool.false_eq_true, ↓reduceIte, Function.comp_apply]
    · have h := SortedDefinableOver.coordinate_eq_term (M := M) (A := A) (Var := Var)
        .rv (.inr i) (rvMulTerm negOne input)
      convert h using 1
      ext a
      change (a .rv (.inr i) = F (a .rv ∘ Sum.inl) i) ↔
        a .rv (.inr i) = (rvMulTerm negOne input).realize M (fun s => Sum.elim Subtype.val (a s))
      simp only [F, changeRVSigns, hs, ↓reduceIte, Function.comp_apply, signedRVNeg,
        M, realize_rvMulTerm, negOne, input, SortedTerm.realize, Sum.elim_inl, Sum.elim_inr]
  have h := hDomain.inter (SortedDefinableOver.iInter hGraph)
  convert h using 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  change (∃ x : signedValuePullback O sign U, x.val = a .rv ∘ Sum.inl ∧ F x.val = a .rv ∘ Sum.inr) ↔
    a .rv ∘ Sum.inl ∈ signedValuePullback O sign U ∧ ∀ i, a .rv (.inr i) = F (a .rv ∘ Sum.inl) i
  exact ⟨fun ⟨x, hx, he⟩ => ⟨hx ▸ x.property, fun i => by rw [← hx]; exact (congrFun he i).symm⟩,
    fun ⟨hx, he⟩ => ⟨⟨a .rv ∘ Sum.inl, hx⟩, rfl, funext fun i => (he i).symm⟩⟩

private theorem signedValuePullback_definable_of_signIndexed [Finite I]
    (U : (I → Bool) → Set (I → Additive O.ValueGroupˣ))
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO power) A
      {x : ∀ s, RVVariables I s → CanonicalSort O s | x .rv ∈ signIndexedValuePullback O hO U}) :
    SortedDefinableOver (canonicalStructure (L := L) O hO power) A
      {x : ∀ s, RVVariables I s → CanonicalSort O s | x .rv ∈ signedValuePullback O sign (U sign)} := by
  let M := canonicalStructure (L := L) O hO power
  let Var := RVVariables I
  let Assign := ∀ s, Var s → CanonicalSort O s
  let guard (i : I) : Set Assign := {a | IsPositiveRV O (changeRVSigns O sign (a .rv) i)}
  have hg (i : I) : SortedDefinableOver M A (guard i) := by
    let term : SortedTerm L E (fun s => (A s : Type z) ⊕ Var s) .rv := .var (.inr i)
    let cmp (x y : SortedTerm L E (fun s => (A s : Type z) ⊕ Var s) .rv) :
        SortedFormula L E (fun s => (A s : Type z) ⊕ Var s) :=
      (.rel .rvLE (Fin.cases x (fun i => by
        have hi : i = 0 := Fin.fin_one_eq_zero i
        subst i
        exact y)) : SortedFormula L E _).neg
    let := rvLinearOrder O hO
    cases hs : sign i
    · refine ⟨cmp term rvZeroTerm, fun a => ?_⟩
      rw [SortedFormula.realize_neg]
      change IsPositiveRV O (changeRVSigns O sign (a .rv) i) ↔
        ¬ term.realize M _ ≤ rvZeroTerm.realize M _
      rw [realize_rvZeroTerm]
      change IsPositiveRV O (changeRVSigns O sign (a .rv) i) ↔ ¬ a .rv i ≤ 0
      simpa only [changeRVSigns, hs, Bool.false_eq_true, ↓reduceIte, not_le] using
        (isPositiveRV_iff_pos O hO (t := a .rv i))
    · refine ⟨cmp rvZeroTerm term, fun a => ?_⟩
      rw [SortedFormula.realize_neg]
      change IsPositiveRV O (changeRVSigns O sign (a .rv) i) ↔
        ¬ rvZeroTerm.realize M _ ≤ term.realize M _
      rw [realize_rvZeroTerm]
      change IsPositiveRV O (changeRVSigns O sign (a .rv) i) ↔ ¬ (0 : RV0 O) ≤ a .rv i
      rw [not_le]
      obtain ⟨x, hx⟩ := rv_surjective O (a .rv i)
      simp only [changeRVSigns, hs, ↓reduceIte, ← hx, signedRVNeg_rv,
        isPositiveRV_rv_iff, neg_pos, rv_lt_zero_iff O hO]
  convert hD.inter (SortedDefinableOver.iInter hg) using 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  change a .rv ∈ signedValuePullback O sign (U sign) ↔
    a .rv ∈ signIndexedValuePullback O hO U ∧
      ∀ i, IsPositiveRV O (changeRVSigns O sign (a .rv) i)
  constructor
  · rintro ⟨hs, hv⟩
    have h i := (changeRVSigns_positive_iff O sign hO (a .rv) i).mp (hs i)
    have he : sign = rvSignPattern O hO (a .rv) := funext fun i => (h i).2
    exact ⟨⟨fun i => (h i).1, he ▸ hv⟩, hs⟩
  · rintro ⟨⟨_, hv⟩, hs⟩
    have he : sign = rvSignPattern O hO (a .rv) :=
      funext fun i => ((changeRVSigns_positive_iff O sign hO (a .rv) i).mp (hs i)).2
    exact ⟨hs, he.symm ▸ hv⟩

/-- The positive-case affine trivializations give the signed result
by gluing the sign pieces over the same base. -/
theorem signIndexedValuePullback_definablyEquivalent [Fintype I] [DecidableEq I] {J : Type} [Finite J]
    (U : (I → Bool) → Set (I → Additive O.ValueGroupˣ)) (target : (I → Bool) → Set (J → RV0 O))
    (hminus : rv O (-1) ∈ A .rv) (tag : Fin (Fintype.card (I → Bool)) ↪ RV0 O)
    (htag : ∀ i, tag i ∈ A .rv)
    (hD : SortedDefinableOver (canonicalStructure (L := L) O hO power) A
      {x : ∀ s, RVVariables I s → CanonicalSort O s | x .rv ∈ signIndexedValuePullback O hO U})
    (hcharts : ∀ s, RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) A
      (positiveValuePullback O (U s)) (target s)) :
    RVDefinablyEquivalent (canonicalStructure (L := L) O hO power) A
      (signIndexedValuePullback O hO U) (taggedRVUnion (target ∘ (Fintype.equivFin (I → Bool)).symm) tag) := by
  let enum := Fintype.equivFin (I → Bool)
  let source := fun i => signedValuePullback O (enum.symm i) (U (enum.symm i))
  have hdisj : Pairwise (fun i j => Disjoint (source i) (source j)) :=
    fun _ _ h => signedValuePullback_pairwise_disjoint O hO U (fun e => h (enum.symm.injective e))
  have hcover : signIndexedValuePullback O hO U = ⋃ j, source j := by
    rw [signIndexedValuePullback_eq_union O hO U]
    ext x
    rw [Set.mem_iUnion, Set.mem_iUnion]
    exact ⟨fun ⟨s, hs⟩ => ⟨enum s, by simpa only [source, Equiv.symm_apply_apply] using hs⟩,
      fun ⟨i, hi⟩ => ⟨enum.symm i, hi⟩⟩
  rw [hcover]
  exact rvDefinablyEquivalent_tagged_union (M := canonicalStructure (L := L) O hO power)
    (A := A) source (target ∘ enum.symm) tag htag hdisj
    (fun i => (signedValuePullback_definablyEquivalent O (enum.symm i) hO power A (U (enum.symm i))
      hminus (signedValuePullback_definable_of_signIndexed O (enum.symm i) hO power A U hD)).trans (hcharts (enum.symm i)))

end GeneralizedEuler.Section2
