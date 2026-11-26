module

public import Section5.FirstPairContractionOrders

/-! Any two orders compare by induction on arity. Move the desired
first coordinate into second place using a tail permutation, then
exchange the first pair and compare orders with a common first head. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  (neg : rv O (-1) ∈ S.carrier .rv)

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem contraction_order_comparison_of_two_coordinates
    (hyp : FieldwiseContractionHypotheses S) (head : HeadPreparationHypotheses O hO power S)
    (pair : TwoCoordinateComparisonAtFieldBases S neg) (n : ℕ) :
    ContractionOrderComparisonAt S neg n := by
  have heads (m k : ℕ) (D : RetainedFieldFamily 𝓜 S (m+1) k) : Nonempty (HeadContractionData D) :=
    head_contraction_data_exists hO power S head.minusOne head.minusOne_realizes head.fieldTerms head.fieldTerms_realize
      D (head.saturated m D.tags D.finiteTags) (head.immediate m)
  let eq := commonBlowup_equivalence (ElementaryClassStep O hO power S neg)
    (fun {_ _ _} => elementaryClassStep_diamond O hO power S neg)
  induction n with
  | zero =>
    intro k l a b A p U V idx idy u v
    have same : p = Equiv.refl _ := Equiv.ext (fun i => i.elim0)
    rw [same,A.permuteVF_refl] at v
    let : Finite A.tags := A.finiteTags
    let it : Fin (Nat.card A.tags) ≃ A.tags := (Finite.equivFin _).symm
    exact fieldwise_contraction_runs_common_blowup S neg hyp u v it it idx idy
      (fun _ => ⟨_,0,0,rfl,rfl⟩)
  | succ n ih =>
    intro k l a b A p U V idx idy left right
    have sameFirst {D : RetainedFieldFamily 𝓜 S (n+1) k} {G H : RetainedFieldFamily 𝓜 S 0 l}
        {d e : ℕ} (i : Fin d ≃ G.tags) (j : Fin e ≃ H.tags)
        (r : Equiv.Perm (Fin (n+1))) (fix : r 0 = 0)
        (g : HeadContractionRun D G) (h : HeadContractionRun (D.permuteVF r) H) :
        terminalCommonBlowup S neg G H i j := by
      obtain ⟨t,rfl⟩ := FinOrder.eq_keepFirst_of_fixes_zero r fix
      exact compare_shared_first_contraction S neg hyp head ih D t i j g h
    by_cases fix : p 0 = 0
    · exact sameFirst idx idy p fix left right
    cases n with
    | zero => exact (fix (Fin.eq_zero (p 0))).elim
    | succ m =>
      let t := Equiv.swap (0 : Fin (m+1)) ((p 0).pred fix)
      let q := FinOrder.keepFirst t
      let swap := Equiv.swap (0 : Fin (m+2)) 1
      let r := swap.trans q
      have q0 : q 0 = 0 := rfl
      have r0 : r 0 = p 0 := by
        have h : swap 0 = 1 := Equiv.swap_apply_left _ _
        change q (swap 0) = p 0
        rw [h]
        change (t 0).succ = p 0
        rw [show t 0 = (p 0).pred fix from Equiv.swap_apply_left _ _,Fin.succ_pred]
      let back := p.trans r.symm
      have back0 : back 0 = 0 := r.symm_apply_eq.2 r0.symm
      have order : back.trans r = p := Equiv.ext (fun i => r.apply_symm_apply (p i))
      obtain ⟨W,w⟩ := HeadContractionRun.exists_run heads (A.permuteVF q)
      obtain ⟨X,x⟩ := HeadContractionRun.exists_run heads (A.permuteVF r)
      have count := left.selected_count
      subst l
      let : Finite W.tags := W.finiteTags
      let : Finite X.tags := X.finiteTags
      let iw : Fin (Nat.card W.tags) ≃ W.tags := (Finite.equivFin _).symm
      let ix : Fin (Nat.card X.tags) ≃ X.tags := (Finite.equivFin _).symm
      have e₁ := sameFirst idx iw q q0 left w
      have x' : HeadContractionRun ((A.permuteVF q).permuteVF swap) X := by
        rw [A.permuteVF_comp]
        exact x
      have e₂ := compare_swapped_first_pair S neg hyp pair (A.permuteVF q) iw ix w x'
      have v' : HeadContractionRun ((A.permuteVF r).permuteVF back) V := by
        rw [A.permuteVF_comp,order]
        exact right
      have e₃ := sameFirst ix idy back back0 x v'
      exact eq.trans e₁ (eq.trans e₂ e₃)

end GeneralizedEuler.Section5
