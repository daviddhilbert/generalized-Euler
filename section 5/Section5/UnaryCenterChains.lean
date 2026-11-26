module

public import Section5.PairedUnaryChains
import all Section5.PairedMixedFocus
import all Section5.PairedSourceTranslation

/-! Apply a finite list of tests by target focus translations on a
unary pullback. The test centers may depend on the retained tag. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

universe u

variable {K : Type u} [Field K] (O : ValuationSubring K)
  {R : Type u} {A : Set (K × R)}

def centerLocus (c : R → K) : Set (RV0 O × R) :=
  {t | (c t.2,t.2) ∈ A ∧ t.1 ≠ 0 ∧ rv O (c t.2) = t.1}

def centerFocus (c : R → K) (a : A) (t : RV0 O × R) : A := by
  classical
  by_cases h : t ∈ centerLocus (A := A) O c
  · exact ⟨(c t.2,t.2),h.1⟩
  · exact a

theorem centerFocus_valid (c : R → K) (a : A) {t : RV0 O × R}
    (ht : t ∈ centerLocus (A := A) O c) : unaryMixedLabel O (centerFocus O c a t).val = t := by
  unfold centerFocus
  rw [dite_eq_left ht]
  exact Prod.ext ht.2.2 rfl

private theorem center_step_decides (c : R → K) (a : A) (full : IsUnaryPullback O A)
    (x y : A)
    (same : unaryMixedLabel O (recodeUnaryTranslation O
      (pairedTargetTranslation O (centerLocus (A := A) O c) (centerFocus O c a)) x.val) =
      unaryMixedLabel O (recodeUnaryTranslation O
        (pairedTargetTranslation O (centerLocus (A := A) O c) (centerFocus O c a)) y.val)) :
    rv O (x.val.1-c x.val.2) = rv O (y.val.1-c y.val.2) := by
  classical
  let C := centerLocus (A := A) O c
  let T := pairedTargetTranslation O C (centerFocus O c a)
  let t := unaryMixedLabel O x.val
  have eq := congrArg (fun p : RV0 O × (R × RV0 O) => (p.2.2,p.2.1)) same
  change unaryMixedLabel O x.val = unaryMixedLabel O y.val at eq
  have fieldEq : rv O x.val.1 = rv O y.val.1 := congrArg Prod.fst eq
  have tagEq : x.val.2 = y.val.2 := congrArg (fun p : RV0 O × R => p.2) eq
  by_cases nz : rv O x.val.1 = 0
  · have z := (rv_eq_zero_iff O).1 nz
    have z' := (rv_eq_zero_iff O).1 (fieldEq.symm.trans nz)
    rw [z,z',tagEq]
  · have nn : x.val.1 ≠ 0 := (rv_eq_zero_iff O).not.1 nz
    by_cases locus : t ∈ C
    · have truth : mixedTargetFocusLabel O C (centerFocus O c a) x =
          mixedTargetFocusLabel O C (centerFocus O c a) y := by
        have he := congrArg (fun p : RV0 O × (R × RV0 O) => p.1) same
        change rv O (T.map (x.val.2,x.val.1)).2.1 = rv O (T.map (y.val.2,y.val.1)).2.1 at he
        rw [pairedTargetTranslation_label O C _ x,pairedTargetTranslation_label O C _ y] at he
        exact he
      have locY : unaryMixedLabel O y.val ∈ C := eq ▸ locus
      unfold mixedTargetFocusLabel at truth
      rw [ite_eq_left locus,ite_eq_left locY] at truth
      unfold centerFocus at truth
      rw [dite_eq_left locus,dite_eq_left locY] at truth
      exact truth
    · have out : c x.val.2 ∉ openDisc O x.val.1 (O.valuation x.val.1) := by
        intro inside
        have lead := (rv_eq_rv_iff_valuation O nn).2 inside
        have label : unaryMixedLabel O x.val = unaryMixedLabel O (c x.val.2,x.val.2) :=
          Prod.ext lead.symm rfl
        exact locus ⟨full x.val x.property _ label,nz,lead⟩
      have hr : O.valuation x.val.1 ≠ 0 := (map_ne_zero O.valuation).2 nn
      rw [← tagEq]
      exact rv_sub_const_of_openDisc_avoids O hr out (mem_openDisc_center O hr x.val.1)
        ((rv_eq_rv_iff_valuation O nn).1 fieldEq.symm)

/-- Each test is expressed in the field coordinate at the stage where
it is applied. The remaining centers are translated by the same
offset, which is available from the retained tag of that stage. -/
theorem unary_target_chain_prepares_centers (centers : List (R → K)) (full : IsUnaryPullback O A) :
    ∃ (R' : Type u) (B : Set (K × R')) (h : A ≃ B),
      UnaryTargetFocusChain O A B h ∧ IsUnaryPullback O B ∧
      ∀ x y : A, unaryMixedLabel O (h x).val = unaryMixedLabel O (h y).val →
        ∀ c ∈ centers, rv O (x.val.1-c x.val.2) = rv O (y.val.1-c y.val.2) := by
  generalize len : centers.length = n
  induction n generalizing R A centers with
  | zero =>
    have he := List.length_eq_zero_iff.mp len
    subst centers
    exact ⟨R,A,Equiv.refl _,.nil A,full,fun _ _ _ _ h => False.elim (List.not_mem_nil h)⟩
  | succ n ih =>
    cases centers with
    | nil => simp at len
    | cons c rest =>
      have hlen : rest.length = n := by simpa using len
      by_cases empty : A.Nonempty
      · let a : A := ⟨empty.choose,empty.choose_spec⟩
        let C := centerLocus (A := A) O c
        let focus := centerFocus O c a
        let T := pairedTargetTranslation O C focus
        let s := unaryImageIso O A T
        have valid (t) (h : t ∈ C) := centerFocus_valid O c a h
        have full' : IsUnaryPullback O (recodeUnaryTranslation O T '' A) :=
          recodeUnaryTranslation_preserves_pullback O T A full
            (fun r t h => congrArg (fun p : RV0 O × R => p.1) (valid (t,r) h))
        let shift (d : R → K) (i : R × RV0 O) := d i.1 - T.offset i.1 i.2
        obtain ⟨R',B,h,chain,pb,decides⟩ := ih (rest.map shift) full' (by simp [hlen])
        refine ⟨R',B,s.trans h,.cons A C focus valid h chain,pb,?_⟩
        intro x y same d hd
        have old := unaryTargetFocusChain_refines O chain (s x) (s y) same
        rcases List.mem_cons.1 hd with he | hd
        · subst d
          exact center_step_decides O c a full x y old
        · have he := decides (s x) (s y) same (shift d) (List.mem_map.2 ⟨d,hd,rfl⟩)
          change rv O ((x.val.1-T.offset x.val.2 (rv O x.val.1))-(d x.val.2-T.offset x.val.2 (rv O x.val.1))) =
            rv O ((y.val.1-T.offset y.val.2 (rv O y.val.1))-(d y.val.2-T.offset y.val.2 (rv O y.val.1))) at he
          simpa only [sub_sub_sub_cancel_right] using he
      · refine ⟨R,A,Equiv.refl _,.nil A,full,?_⟩
        intro x
        exact False.elim (empty ⟨x.val,x.property⟩)

end GeneralizedEuler.Section5
