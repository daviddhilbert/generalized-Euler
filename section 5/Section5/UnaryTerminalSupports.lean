module

public import Section5.UnaryHeadContractionComparison
import all Section4.Objects

/-! Splitting by the old support and the new lead enumerates exactly
the zero patterns in the standard terminal graded object. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {k : ℕ}

@[expose] def extendTerminalSupport (old : Finset (Fin k)) (new : Bool) : Finset (Fin (k+1)) :=
  let base := old.map Fin.castSuccEmb
  if new then insert (Fin.last k) base else base

theorem castSucc_mem_extendTerminalSupport (old : Finset (Fin k)) (new : Bool) (i : Fin k) :
    i.castSucc ∈ extendTerminalSupport old new ↔ i ∈ old := by
  classical
  cases new <;> simp [extendTerminalSupport,Fin.castSucc_ne_last]

theorem last_mem_extendTerminalSupport (old : Finset (Fin k)) (new : Bool) :
    Fin.last k ∈ extendTerminalSupport old new ↔ new = true := by
  classical
  have absent : Fin.last k ∉ old.map Fin.castSuccEmb := by
    rw [Finset.mem_map]
    rintro ⟨i,_,eq⟩
    exact Fin.castSucc_ne_last i eq
  cases new <;> simp [extendTerminalSupport,absent]

theorem card_extendTerminalSupport (old : Finset (Fin k)) (new : Bool) :
    (extendTerminalSupport old new).card = old.card+new.toNat := by
  classical
  have absent : Fin.last k ∉ old.map Fin.castSuccEmb := by
    rw [Finset.mem_map]
    rintro ⟨i,_,eq⟩
    exact Fin.castSucc_ne_last i eq
  cases new
  · simp [extendTerminalSupport,Bool.toNat]
  · simp [extendTerminalSupport,Finset.card_insert_of_notMem absent,Bool.toNat]

/-- Split a pattern into its old selected coordinates and the support
of its last coordinate. -/
@[expose] def unaryTerminalSupportEquiv : (Finset (Fin k) × Bool) ≃ Finset (Fin (k+1)) := by
  classical
  refine ⟨fun p => extendTerminalSupport p.1 p.2,
    fun u => ⟨Finset.univ.filter (fun i : Fin k => i.castSucc ∈ u),decide (Fin.last k ∈ u)⟩,?_,?_⟩
  · rintro ⟨old,new⟩
    apply Prod.ext
    · ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,castSucc_mem_extendTerminalSupport]
    · apply Bool.eq_iff_iff.2
      exact decide_eq_true_iff.trans (last_mem_extendTerminalSupport old new)
  · intro u
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (last_mem_extendTerminalSupport _ _).trans decide_eq_true_iff
    · rw [castSucc_mem_extendTerminalSupport]
      simp

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {a : ℕ}

theorem RetainedFieldFamily.terminalUnaryPiece_class_eq_support
    (B : RetainedFieldFamily M S 0 (k+1)) (tags : Fin a ≃ B.tags)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (old : Finset (Fin k)) (new : Bool) :
    let t := Fintype.card {i // i ∈ old}
    let keep := Subtype.val ∘ (Fintype.equivFin {i // i ∈ old}).symm
    objectClass M S ⟨t+new.toNat,B.terminalPiece tags (terminalUnaryKeep keep new) zero hz⟩ =
      objectClass M S (B.terminalGradedPiece tags (extendTerminalSupport old new) zero hz) := by
  intro t keep
  let U := B.terminalPiece tags (terminalUnaryKeep keep new) zero hz
  let V := B.terminalGradedPiece tags (extendTerminalSupport old new) zero hz
  have card : V.1 = t+new.toNat := by
    change Fintype.card {i // i ∈ extendTerminalSupport old new} = Fintype.card {i // i ∈ old}+new.toNat
    rw [Fintype.card_coe,Fintype.card_coe,card_extendTerminalSupport]
  have oldRange (i : Fin k) : i ∈ Set.range keep ↔ i ∈ old := by
    let e := (Fintype.equivFin {i // i ∈ old}).symm
    constructor
    · rintro ⟨j,rfl⟩
      exact (e j).property
    · intro hi
      exact ⟨e.symm ⟨i,hi⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩
  have eqCarrier : U.carrier = V.2.carrier := by
    ext x
    have cv := B.terminalGradedPiece_mem tags (extendTerminalSupport old new) zero hz x
    have cu := B.terminalUnaryPiece_mem tags keep zero hz new x
    refine cu.trans (Iff.trans ?_ cv.symm)
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨prev,tail⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact tail.trans (last_mem_extendTerminalSupport old new).symm
      · exact (prev j).trans ((oldRange j).trans (castSucc_mem_extendTerminalSupport old new j).symm)
    · intro every
      exact ⟨fun i => (every i.castSucc).trans ((castSucc_mem_extendTerminalSupport old new i).trans (oldRange i).symm),
        (every (Fin.last k)).trans (last_mem_extendTerminalSupport old new)⟩
  have iso : RVDefinablyEquivalent M S.carrier U.carrier V.2.carrier := by
    rw [eqCarrier]
    exact ⟨Equiv.refl _,definable_identity_label M S V.2.definable⟩
  have same {d e : ℕ} (X : RVObject M S d) (Y : RVObject M S e) (degree : e = d)
      (h : RVDefinablyEquivalent M S.carrier X.carrier Y.carrier) :
      objectClass M S ⟨d,X⟩ = objectClass M S ⟨e,Y⟩ := by
    subst e
    exact scissors_sound M S (.iso X Y h)
  exact same U V.2 card iso

attribute [local simp] Bool.toNat_false Bool.toNat_true

@[expose] def RetainedFieldFamily.terminalGradedClass {n : ℕ}
    (B : RetainedFieldFamily M S 0 n) (tags : Fin a ≃ B.tags)
    (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun i => i.elim0)) : RVSemiring M S :=
  ∑ support : Finset (Fin n), objectClass M S (B.terminalGradedPiece tags support zero hz)

section Canonical

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S₀ : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem RetainedFieldFamily.terminalUnaryPatternClass_sum
    (B : RetainedFieldFamily 𝓜 S₀ 0 (k+1)) (tags : Fin a ≃ B.tags)
    (zero : S₀.carrier .rv) (hz : zero.val = 0) :
    let keep (s : Finset (Fin k)) := Subtype.val ∘ (Fintype.equivFin {i // i ∈ s}).symm
    (∑ s : Finset (Fin k), B.terminalUnaryPatternClass O hO power S₀ tags zero hz (keep s)) =
      B.terminalGradedClass tags zero hz := by
  intro keep
  let cls (s : Finset (Fin (k+1))) := objectClass 𝓜 S₀ (B.terminalGradedPiece tags s zero hz)
  have each (s : Finset (Fin k)) :
      B.terminalUnaryPatternClass O hO power S₀ tags zero hz (keep s) =
        ∑ b : Bool, cls (extendTerminalSupport s b) := by
    rw [Fintype.sum_bool,terminalUnaryPatternClass]
    have lo := B.terminalUnaryPiece_class_eq_support tags zero hz s false
    have hi := B.terminalUnaryPiece_class_eq_support tags zero hz s true
    exact (congrArg₂ (· + ·) lo hi).trans (add_comm _ _)
  calc
    _ = ∑ s : Finset (Fin k), ∑ b : Bool, cls (extendTerminalSupport s b) := Finset.sum_congr rfl (fun s _ => each s)
    _ = ∑ u : Finset (Fin k) × Bool, cls (unaryTerminalSupportEquiv u) :=
      (Fintype.sum_prod_type (fun u : Finset (Fin k) × Bool => cls (extendTerminalSupport u.1 u.2))).symm
    _ = B.terminalGradedClass tags zero hz := Fintype.sum_equiv unaryTerminalSupportEquiv _ _ (fun _ => rfl)

theorem unary_head_terminal_classes_common_blowup {b : ℕ}
    {A : RetainedFieldFamily 𝓜 S₀ 1 k} (H J : HeadContractionData (n := 0) A)
    (hyp : UnaryHeadComparisonHypotheses O hO power S₀ H J) (neg : rv O (-1) ∈ S₀.carrier .rv)
    (zero : S₀.carrier .rv) (hz : zero.val = 0)
    (tagsH : Fin a ≃ H.target.tags) (tagsJ : Fin b ≃ J.target.tags) :
    CommonBlowup (ElementaryClassStep O hO power S₀ neg)
      (H.target.terminalGradedClass tagsH zero hz) (J.target.terminalGradedClass tagsJ zero hz) := by
  have h := unary_head_contractions_common_blowup O hO power S₀ H J hyp neg zero hz tagsH tagsJ
    (H.head_slices_equivalent J)
  simpa only [RetainedFieldFamily.terminalUnaryPatternClass_sum] using h

theorem unary_head_terminal_classes_common_blowup_of_iso {b : ℕ}
    {A B : RetainedFieldFamily 𝓜 S₀ 1 k} (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B)
    (hyp : UnaryHeadComparisonHypotheses O hO power S₀ H J) (neg : rv O (-1) ∈ S₀.carrier .rv)
    (zero : S₀.carrier .rv) (hz : zero.val = 0)
    (tagsH : Fin a ≃ H.target.tags) (tagsJ : Fin b ≃ J.target.tags)
    (e : MixedGraphIso 𝓜 S₀
      {x : SortedAssignment (CanonicalSort O) (MixedVariables 1 A.tags) | mixedTuple x ∈ A.carrier}
      {y : SortedAssignment (CanonicalSort O) (MixedVariables 1 B.tags) | mixedTuple y ∈ B.carrier})
    (preserve : ∀ x, (e.equiv x).val .rv ∘ B.select = x.val .rv ∘ A.select) :
    CommonBlowup (ElementaryClassStep O hO power S₀ neg)
      (H.target.terminalGradedClass tagsH zero hz) (J.target.terminalGradedClass tagsJ zero hz) := by
  have h := unary_head_contractions_common_blowup O hO power S₀ H J hyp neg zero hz tagsH tagsJ
    (fun p => H.head_slices_equivalent_of_source_equiv J p (A.selectedFibers_equivalent_of_iso B e preserve p))
  simpa only [RetainedFieldFamily.terminalUnaryPatternClass_sum] using h

end Canonical

end GeneralizedEuler.Section5
