module

public import Section5.ProductTerminalTags
public import Section5.UnaryTerminalSupports
import all Section4.Objects
import all Section4.Scissors

/-! The terminal class of an independent two-coordinate run is the
product of the unary endpoint classes, including zero leading terms. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {a b m : ℕ}

namespace HeadContractionData

variable {A B : RetainedFieldFamily M S 1 0}
  (H : HeadContractionData (n := 0) A) (J : HeadContractionData (n := 0) B)
  (idx : Fin a ≃ H.target.tags) (idy : Fin b ≃ J.target.tags)

@[expose] def productTerminalIndex : Fin (a+b) ≃ (H.productSecond J).target.tags :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr idx idy).trans (H.productTagPack J).symm)

variable (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))

set_option maxHeartbeats 900000 in
theorem productTerminalPiece_class (old : Finset (Fin 1)) (new : Bool) :
    let C := H.target.terminalGradedPiece idx old zero hz
    let D := J.target.terminalGradedPiece idy (extendTerminalSupport (∅ : Finset (Fin 0)) new) zero hz
    objectClass M S ((H.productSecond J).target.terminalGradedPiece (H.productTerminalIndex J idx idy)
      (extendTerminalSupport old new) zero hz) = objectClass M S C * objectClass M S D := by
  intro C D
  let T := (H.productSecond J).target
  let pack := H.productTerminalIndex J idx idy
  let W := T.terminalGradedPiece pack (extendTerminalSupport old new) zero hz
  have count : W.1 = C.1+D.1 := by
    change Fintype.card {i // i ∈ extendTerminalSupport old new} =
      Fintype.card {i // i ∈ old}+Fintype.card {i // i ∈ extendTerminalSupport (∅ : Finset (Fin 0)) new}
    rw [Fintype.card_coe,Fintype.card_coe,Fintype.card_coe,card_extendTerminalSupport,card_extendTerminalSupport]
    simp
  have pre := rv_reindex_equivalent M S (finSumFinEquiv (m := a) (n := b)).symm
    (productSet C.2.carrier D.2.carrier) (rv_product_definable C.2.definable D.2.definable)
  have eq : {t : Fin (a+b) → RV0 O | t ∘ finSumFinEquiv ∈ productSet C.2.carrier D.2.carrier} = W.2.carrier := by
    ext t
    let x : Fin a → RV0 O := t ∘ rvHead
    let y : Fin b → RV0 O := t ∘ rvTail
    let u := t ∘ pack.symm
    have aTags : u ∘ (H.productTagPack J).symm ∘ Sum.inl = x ∘ idx.symm := by
      funext i
      simp [u,pack,productTerminalIndex,x,rvHead,Function.comp_apply]
    have bTags : u ∘ (H.productTagPack J).symm ∘ Sum.inr = y ∘ idy.symm := by
      funext i
      simp [u,pack,productTerminalIndex,y,rvTail,Function.comp_apply]
    have tags : t ∈ T.terminalLabels pack ↔ x ∈ H.target.terminalLabels idx ∧ y ∈ J.target.terminalLabels idy := by
      change (Fin.elim0,u) ∈ T.carrier ↔ _
      rw [H.productSecond_target_mem J u,aTags,bTags]
      rfl
    have oldLead (i : Fin 1) : t (T.terminalSelect pack i.castSucc) = x (H.target.terminalSelect idx i) := by
      rw [Fin.fin_one_eq_zero i]
      change u (T.select 0) = x (idx.symm (H.target.select 0))
      have e : (H.productTagPack J).symm (Sum.inl (H.target.select 0)) = T.select 0 :=
        (Equiv.symm_apply_eq _).2 (H.productTagPack_select_zero J).symm
      rw [← e]
      exact congrFun aTags _
    have newLead : t (T.terminalSelect pack (Fin.last 1)) = y (J.target.terminalSelect idy 0) := by
      change u (T.select 1) = y (idy.symm (J.target.select 0))
      have e : (H.productTagPack J).symm (Sum.inr (J.target.select 0)) = T.select 1 :=
        (Equiv.symm_apply_eq _).2 (H.productTagPack_select_one J).symm
      rw [← e]
      exact congrFun bTags _
    have memW := T.terminalGradedPiece_mem pack (extendTerminalSupport old new) zero hz t
    have memC := H.target.terminalGradedPiece_mem idx old zero hz x
    have memD := J.target.terminalGradedPiece_mem idy (extendTerminalSupport (∅ : Finset (Fin 0)) new) zero hz y
    change x ∈ C.2.carrier ∧ y ∈ D.2.carrier ↔ t ∈ W.2.carrier
    refine (and_congr memC memD).trans (Iff.trans ?_ memW.symm)
    rw [tags]
    constructor
    · rintro ⟨⟨ht,hOld⟩,⟨hu,hNew⟩⟩
      refine ⟨⟨ht,hu⟩,fun i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [newLead,last_mem_extendTerminalSupport]
        exact (hNew (Fin.last 0)).trans (last_mem_extendTerminalSupport _ _)
      · rw [oldLead,castSucc_mem_extendTerminalSupport]
        exact hOld j
    · rintro ⟨⟨ht,hu⟩,h⟩
      refine ⟨⟨ht,fun i => ?_⟩,⟨hu,fun i => ?_⟩⟩
      · have each := h i.castSucc
        rwa [oldLead,castSucc_mem_extendTerminalSupport] at each
      · rw [Fin.fin_one_eq_zero i]
        have last := h (Fin.last 1)
        rw [newLead,last_mem_extendTerminalSupport] at last
        exact last.trans (last_mem_extendTerminalSupport _ _).symm
  have iso : RVDefinablyEquivalent M S.carrier (productSet C.2.carrier D.2.carrier) W.2.carrier := eq ▸ pre
  have mulClass {e : ℕ} (Y : RVObject M S e) (d : e = C.1+D.1)
      (h : RVDefinablyEquivalent M S.carrier (productSet C.2.carrier D.2.carrier) Y.carrier) :
      objectClass M S ⟨e,Y⟩ = objectClass M S C * objectClass M S D := by
    subst e
    unfold objectClass
    rw [← map_mul]
    exact scissors_sound M S (RVRelation.prod C.2 D.2 Y h)
  exact mulClass W.2 count iso

theorem unaryProduct_terminalClass_mul (pack : Fin m ≃ (H.productSecond J).target.tags) :
    (H.productSecond J).target.terminalGradedClass pack zero hz =
      H.target.terminalGradedClass idx zero hz * J.target.terminalGradedClass idy zero hz := by
  rw [(H.productSecond J).target.terminalGradedClass_reindex pack (H.productTerminalIndex J idx idy) zero hz]
  let f (s : Finset (Fin 2)) := objectClass M S ((H.productSecond J).target.terminalGradedPiece
    (H.productTerminalIndex J idx idy) s zero hz)
  let a (s : Finset (Fin 1)) := objectClass M S (H.target.terminalGradedPiece idx s zero hz)
  let b (s : Finset (Fin 1)) := objectClass M S (J.target.terminalGradedPiece idy s zero hz)
  have one : J.target.terminalGradedClass idy zero hz =
      b (extendTerminalSupport (∅ : Finset (Fin 0)) false) + b (extendTerminalSupport (∅ : Finset (Fin 0)) true) := by
    let : Unique (Finset (Fin 0)) := ⟨⟨∅⟩,fun s => Finset.eq_empty_of_forall_notMem (fun i => i.elim0)⟩
    have eq := sum_extendTerminalSupport (k := 0) b
    rw [Fintype.sum_unique,Fintype.sum_unique] at eq
    exact eq.symm
  change (∑ s, f s) = (∑ s, a s) * J.target.terminalGradedClass idy zero hz
  rw [one,← sum_extendTerminalSupport f,mul_add,Finset.sum_mul,Finset.sum_mul]
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl (fun s _ => H.productTerminalPiece_class J idx idy zero hz s false))
    (Finset.sum_congr rfl (fun s _ => H.productTerminalPiece_class J idx idy zero hz s true))

end HeadContractionData

end GeneralizedEuler.Section5
