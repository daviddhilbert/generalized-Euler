module

public import Section5.TranslatedBlowupObjects
public import Section5.RelativeTranslation
public import Section5.FocusDeletionFiniteness
public import Mathlib.Data.Fin.Tuple.Basic

/-! On a pullback locus, a focus translation gives the two graded
pieces of the elementary blowup. The original leading term at the
translated coordinate is retained and is determined by the old tag. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k m : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1))
  (j : Fin (k+1))

local notation "𝓜" => canonicalStructure (L := L) O hO power

abbrev RetainedFocusTuple := (Fin k → K) × U.carrier

@[expose] def focusTranslationSource : Set (RetainedFocusTuple O hO power S U × K) :=
  {x | U.label x.1.2 ∘ j.succAbove = rv O ∘ x.1.1 ∧ rv O x.2 = U.label x.1.2 j}

@[expose] def focusTranslationTarget : Set (RetainedFocusTuple O hO power S U × (K × RV0 O)) :=
  {y | U.label y.1.2 ∘ j.succAbove = rv O ∘ y.1.1 ∧ y.2.2 = U.label y.1.2 j ∧
    unsignedValue O (rv O y.2.1) < unsignedValue O y.2.2}

/-- Focuses may vary with the retained field tuple and the old RV tag.
The output condition only uses the structure map and the new leading
term, and hence describes full RV fibers. -/
theorem focus_translation_image
    (c : (Fin k → K) → U.carrier → K)
    (valid : ∀ x u, U.label u ∘ j.succAbove = rv O ∘ x → rv O (c x u) = U.label u j) :
    (fun a : RetainedFocusTuple O hO power S U × K => (a.1,a.2 - c a.1.1 a.1.2,rv O a.2)) ''
      focusTranslationSource O hO power S U j = focusTranslationTarget O hO power S U j := by
  let base (x : RetainedFocusTuple O hO power S U) := (rv O ∘ x.1,x.2)
  let T : RelativeTranslation O base := ⟨Set.univ,fun x _ => c x.1 x.2⟩
  let A : Set (((Fin k → RV0 O) × U.carrier) × RV0 O) :=
    {w | U.label w.1.2 ∘ j.succAbove = w.1.1 ∧ w.2 = U.label w.1.2 j}
  have image := T.image_pullback A (by
    intro x t h _
    have ht : t = U.label x.2 j := h.2
    exact ⟨ht ▸ U.nonzero x.2 j, (valid x.1 x.2 h.1).trans ht.symm⟩)
  have mapEq : T.map = fun a => (a.1,a.2 - c a.1.1 a.1.2,rv O a.2) := by
    funext a
    simp [T,RelativeTranslation.map,RelativeTranslation.offset]
  rw [mapEq] at image
  convert image using 1
  · rfl
  ext y
  change (_ ∧ _ ∧ unsignedValue O (rv O y.2.1) < unsignedValue O y.2.2) ↔
    (_ ∧ _) ∧ ((True ∧ _) ∨ (¬ True ∧ _))
  simp only [base,true_and,not_true_eq_false,false_and,or_false,and_assoc]

variable (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite)

theorem focus_target_zero_stratum
    (y : RetainedFocusTuple O hO power S U × (K × RV0 O)) (hy : y.2.1 = 0) :
    let Z := zeroBlowupObject U j finiteDelete
    let z : SortedAssignment (CanonicalSort O) (ObjectLift.Vars Z) :=
      fun s => match s with
      | .vf => y.1.1
      | .rv => y.1.2.val
    (y ∈ focusTranslationTarget O hO power S U j) ↔
      z ∈ ObjectLift.carrier Z ∧ y.2.2 = U.label y.1.2 j := by
  intro Z z
  have hproj : (canonicalStructure (L := L) O hO power).rvMap ∘ (z .vf) = rv O ∘ y.1.1 :=
    funext fun _ => canonicalStructure_rvMap O hO power _
  constructor
  · rintro ⟨h,ht,_⟩
    exact ⟨⟨y.1.2,rfl,h.trans hproj.symm⟩,ht⟩
  · rintro ⟨⟨a,ha,hw⟩,ht⟩
    have eq : a = y.1.2 := Subtype.ext ha
    subst a
    refine ⟨hw.trans hproj,ht,?_⟩
    rw [hy,map_zero,ht,map_zero]
    exact pos_iff_ne_zero.2 ((map_ne_zero _).2 (U.nonzero _ j))

theorem focus_target_positive_stratum
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv)
    (y : RetainedFocusTuple O hO power S U × (K × RV0 O)) (hy : y.2.1 ≠ 0) :
    let P := translatedPositiveObject O hO power S U idx j hneg finiteDelete
    let z : SortedAssignment (CanonicalSort O) (ObjectLift.Vars P) :=
      fun s => match s with
      | .vf => j.insertNth y.2.1 y.1.1
      | .rv => Sum.elim y.1.2.val (fun _ : Fin 1 => rv O y.2.1) ∘ idx
    (y ∈ focusTranslationTarget O hO power S U j) ↔
      z ∈ ObjectLift.carrier P ∧ y.2.2 = U.label y.1.2 j := by
  intro P z
  have old : (z .rv) ∘ blowupOldIndices idx = y.1.2.val := by
    funext i
    change (Sum.elim y.1.2.val (fun _ : Fin 1 => rv O y.2.1) ∘ idx) (idx.symm (.inl i)) = _
    rw [Function.comp_apply,Equiv.apply_symm_apply,Sum.elim_inl]
  have fresh : z .rv (blowupExtraIndex idx) = rv O y.2.1 := by
    change (Sum.elim y.1.2.val (fun _ : Fin 1 => rv O y.2.1) ∘ idx) (idx.symm (.inr 0)) = _
    rw [Function.comp_apply,Equiv.apply_symm_apply,Sum.elim_inr]
  have lead (i : Fin (k+1)) : (canonicalStructure (L := L) O hO power).rvMap (z .vf i) =
      rv O (Fin.insertNth (α := fun _ => K) j y.2.1 y.1.1 i) := by
    change (canonicalStructure (L := L) O hO power).rvMap
      (Fin.insertNth (α := fun _ => K) j y.2.1 y.1.1 i) = _
    rw [canonicalStructure_rvMap]
  constructor
  · rintro ⟨hr,ht,hv⟩
    have tag : z .rv ∈ P.carrier := by
      change ∃ a : U.carrier, a.val = z .rv ∘ blowupOldIndices idx ∧
        unsignedValue O (z .rv (blowupExtraIndex idx)) < unsignedValue O (U.label a j) ∧
        z .rv (blowupExtraIndex idx) ≠ 0
      rw [old,fresh]
      exact ⟨y.1.2,rfl,ht ▸ hv,(rv_eq_zero_iff O).not.2 hy⟩
    let a : P.carrier := ⟨z .rv,tag⟩
    have eq : a.property.choose = y.1.2 := Subtype.ext (a.property.choose_spec.1.trans old)
    refine ⟨⟨a,rfl,?_⟩,ht⟩
    funext i
    change Function.update (U.label a.property.choose) j (z .rv (blowupExtraIndex idx)) i =
      (canonicalStructure (L := L) O hO power).rvMap (z .vf i)
    rw [eq,lead,fresh]
    refine j.succAboveCases ?_ (fun l => ?_) i
    · rw [Function.update_self,Fin.insertNth_apply_same]
    · rw [Function.update_of_ne (Fin.succAbove_ne j l),Fin.insertNth_apply_succAbove]
      exact congrFun hr l
  · rintro ⟨⟨a,ha,hl⟩,ht⟩
    have e : a.property.choose = y.1.2 := Subtype.ext
      (a.property.choose_spec.1.trans ((congrArg (· ∘ blowupOldIndices idx) ha).trans old))
    have mult : a.val (blowupExtraIndex idx) = rv O y.2.1 := (congrFun ha _).trans fresh
    refine ⟨?_,ht,?_⟩
    · funext i
      have hh := congrFun hl (j.succAbove i)
      change Function.update (U.label a.property.choose) j (a.val (blowupExtraIndex idx))
        (j.succAbove i) = (canonicalStructure (L := L) O hO power).rvMap (z .vf (j.succAbove i)) at hh
      rw [e,Function.update_of_ne (Fin.succAbove_ne j i),lead,Fin.insertNth_apply_succAbove] at hh
      exact hh
    · have hh := a.property.choose_spec.2.1
      change unsignedValue O (a.val (blowupExtraIndex idx)) < unsignedValue O (U.label a.property.choose j) at hh
      calc
        unsignedValue O (rv O y.2.1) = unsignedValue O (a.val (blowupExtraIndex idx)) := congrArg (unsignedValue O) mult.symm
        _ < unsignedValue O (U.label a.property.choose j) := hh
        _ = unsignedValue O y.2.2 := congrArg (fun u : U.carrier => unsignedValue O (U.label u j)) e |>.trans
          (congrArg (unsignedValue O) ht.symm)

end GeneralizedEuler.Section5
