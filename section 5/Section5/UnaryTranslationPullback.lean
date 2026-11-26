module

public import Section5.PairedSourceTranslation

/-! Retaining the old RV tag and leading term makes each unary focus
translation a map of pullbacks. A zero fiber stays a singleton. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K) {R : Type*}

@[expose] def IsUnaryPullback (A : Set (K × R)) : Prop :=
  ∀ x ∈ A, ∀ y, unaryMixedLabel O x = unaryMixedLabel O y → y ∈ A

@[expose] def recodeUnaryTranslation (T : RelativeTranslation O (id : R → R)) (x : K × R) :
    K × (R × RV0 O) :=
  (x.1 - T.offset x.2 (rv O x.1),(x.2,rv O x.1))

theorem recodeUnaryTranslation_injective (T : RelativeTranslation O (id : R → R)) :
    Function.Injective (recodeUnaryTranslation O T) := by
  intro x y eq
  have h : T.map (x.2,x.1) = T.map (y.2,y.1) :=
    congrArg (fun q : K × (R × RV0 O) => (q.2.1,q.1,q.2.2)) eq
  exact Prod.swap_injective (T.map_injective h)

theorem recodeUnaryTranslation_zero (T : RelativeTranslation O (id : R → R))
    (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t) (x : K × R) (hx : x.1 = 0) :
    (recodeUnaryTranslation O T x).1 = 0 := by
  classical
  change x.1 - T.offset x.2 (rv O x.1) = 0
  rw [hx,map_zero]
  unfold RelativeTranslation.offset
  dsimp only [id]
  by_cases h : (x.2,0) ∈ T.locus
  · rw [ite_eq_left h,(rv_eq_zero_iff O).1 (valid _ _ h),sub_zero]
  · rw [ite_eq_right h,sub_zero]

theorem recodeUnaryTranslation_preserves_pullback (T : RelativeTranslation O (id : R → R))
    (A : Set (K × R)) (whole : IsUnaryPullback O A)
    (valid : ∀ r t, (r,t) ∈ T.locus → rv O (T.focus r t) = t) :
    IsUnaryPullback O (recodeUnaryTranslation O T '' A) := by
  classical
  rintro _ ⟨x,hx,rfl⟩ y equal
  let t := rv O x.1
  let c := T.offset x.2 t
  have rvEq : rv O (x.1-c) = rv O y.1 := congrArg Prod.fst equal
  have tagEq : x.2 = y.2.1 := congrArg (fun q : RV0 O × (R × RV0 O) => q.2.1) equal
  have leadEq : t = y.2.2 := congrArg (fun q : RV0 O × (R × RV0 O) => q.2.2) equal
  have recovered : rv O (y.1+c) = t := by
    by_cases locus : (x.2,t) ∈ T.locus
    · have val : rv O c = t := by
        change rv O (if (id x.2,t) ∈ T.locus then T.focus x.2 t else 0) = t
        simp only [id_eq,ite_eq_left locus,valid _ _ locus]
      by_cases tz : t = 0
      · have cz : c = 0 := (rv_eq_zero_iff O).1 (val.trans tz)
        rw [cz,add_zero]
        simpa only [cz,sub_zero] using rvEq.symm
      · have hx' : rv O ((x.1-c)+c) = t := by
          rw [sub_add_cancel]
        have hv := (RelativeTranslation.focus_translation_iff (O := O) tz val).1 hx'
        apply (RelativeTranslation.focus_translation_iff (O := O) tz val).2
        simpa only [← unsignedValue_rv,rvEq] using hv
    · have cz : c = 0 := by
        change (if (id x.2,t) ∈ T.locus then T.focus x.2 t else 0) = 0
        simp only [id_eq,ite_eq_right locus]
      rw [cz,add_zero]
      simpa only [cz,sub_zero] using rvEq.symm
  let v := (y.1+c,x.2)
  have vLabel : unaryMixedLabel O x = unaryMixedLabel O v := Prod.ext recovered.symm rfl
  refine ⟨v,whole x hx v vLabel,?_⟩
  change ((y.1+c)-T.offset x.2 (rv O (y.1+c)),(x.2,rv O (y.1+c))) = y
  rw [recovered]
  exact Prod.ext (add_sub_cancel_right _ _) (Prod.ext tagEq leadEq)

end GeneralizedEuler.Section5
