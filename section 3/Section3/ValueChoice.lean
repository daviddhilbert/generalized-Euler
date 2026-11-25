module

public import Section3.SplittingValues
public import Section2.PowerBounded

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

variable {Γ : Type*} [LinearOrder Γ] [OrderBot Γ] [DenselyOrdered Γ] [NoMaxOrder Γ]

/-- A unary value set with a first component has either a least element
or an interval immediately above its infimum. The value sort includes zero. -/
private def HasFirstValueInterval (S : Set Γ) : Prop :=
  ∃ a, IsGLB S a ∧ (a ∈ S ∨ ∃ b, a < b ∧ Ioo a b ⊆ S)

private theorem firstValueInterval_of_cells {S : Set Γ} (hne : S.Nonempty)
    (hc : ∃ C : Finset (Set Γ), (∀ T ∈ C, IsUnaryCell T) ∧ S = ⋃ T ∈ C, T) :
    HasFirstValueInterval S := by
  classical
  obtain ⟨C,hc,rfl⟩ := hc
  induction C using Finset.induction with
  | empty => simp at hne
  | insert D C hDC ih =>
    simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left] at *
    by_cases hd : D.Nonempty
    · have one : HasFirstValueInterval D := by
        rcases hc D (Or.inl rfl) with rfl | ⟨a,rfl⟩ | ⟨b,rfl⟩ | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
        · exact ⟨⊥,isGLB_univ,Or.inl trivial⟩
        · exact ⟨a,isGLB_singleton,Or.inl rfl⟩
        · obtain ⟨x,hx⟩ := hd
          have hb : ⊥ ∈ Iio b := bot_le.trans_lt hx
          exact ⟨⊥,⟨fun _ _ => bot_le,fun _ h => h hb⟩,Or.inl hb⟩
        · obtain ⟨b,hb⟩ := exists_gt a
          exact ⟨a,isGLB_Ioi,Or.inr ⟨b,hb,fun _ h => h.1⟩⟩
        · exact ⟨a,isGLB_Ioo (nonempty_Ioo.mp hd),Or.inr ⟨b,nonempty_Ioo.mp hd,Subset.rfl⟩⟩
      by_cases hn : (⋃ T ∈ C, T).Nonempty
      · obtain ⟨a,ha,hg⟩ := one
        obtain ⟨b,hb,hh⟩ := ih (fun T h => hc T (Or.inr h)) hn
        have liftGerm {x : Γ} {P Q : Set Γ} (h : P ⊆ Q)
            (g : x ∈ P ∨ ∃ y, x < y ∧ Ioo x y ⊆ P) :
            x ∈ Q ∨ ∃ y, x < y ∧ Ioo x y ⊆ Q :=
          g.imp (fun hx => h hx) (fun ⟨y,hy,hs⟩ => ⟨y,hy,hs.trans h⟩)
        rcases le_total a b with h | h
        · exact ⟨a,by simpa [inf_eq_left.mpr h] using ha.union hb,liftGerm subset_union_left hg⟩
        · exact ⟨b,by simpa [inf_eq_right.mpr h] using ha.union hb,liftGerm subset_union_right hh⟩
      · rwa [not_nonempty_iff_eq_empty.mp hn,union_empty]
    · rw [not_nonempty_iff_eq_empty.mp hd,empty_union] at hne ⊢
      exact ih (fun T h => hc T (Or.inr h)) hne

variable {K : Type*} [Field K] {L : Language} [L.Structure K] (O : ValuationSubring K)
  (P : Set K) {F : FieldTerms (convexLanguage L)}
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)

/-- Definability of a value set by pullback to field representatives. -/
abbrev ValueDefinable (S : Set O.ValueGroup) := letI := convexStructure O L
  P.Definable₁ (convexLanguage L) (O.valuation ⁻¹' S)

include hF in
private theorem definable_value_bounds {S : Set O.ValueGroup} (hS : ValueDefinable (L := L) O P S)
    (upper : Bool) : ValueDefinable (L := L) O P (if upper then upperBounds S else lowerBounds S) := by
  let := convexStructure O L
  obtain ⟨φ,hφ⟩ := hS
  let J := convexLanguage L
  let x : J.Term (Fin 1 ⊕ Unit) := .var (.inl 0)
  let y : J.Term (Fin 1 ⊕ Unit) := .var (.inr ())
  let cmp := if upper then valuationLEFormula F y x else valuationLEFormula F x y
  refine ⟨Formula.iAlls Unit ((φ.relabel (fun _ => .inr ())).imp
    ((J.lhomWithConstants P).onFormula cmp)),?_⟩
  ext v
  have hs (s : Unit → K) : φ.Realize (Sum.elim v s ∘ fun _ => Sum.inr ()) ↔
      O.valuation (s ()) ∈ S := (Set.ext_iff.mp hφ _).symm
  have ev (s : Unit → K) : cmp.Realize (Sum.elim v s) ↔
      (if upper then O.valuation (s ()) ≤ O.valuation (v 0)
       else O.valuation (v 0) ≤ O.valuation (s ())) := by
    cases upper <;> simp [cmp,x,y,realize_valuationLEFormula O hF]
  simp only [mem_ofPred_eq,Formula.realize_iAlls,Formula.realize_imp,Formula.realize_relabel,
    LHom.realize_onFormula,hs,ev]
  cases upper <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    constructor
  all_goals first
    | exact fun h s hs => h hs
    | intro h r hr
      obtain ⟨w,rfl⟩ := O.valuation_surjective r
      exact h (fun _ => w) hr

include hF in
private theorem definable_glb {S : Set O.ValueGroup} (hS : ValueDefinable (L := L) O P S)
    {r : O.ValueGroup} (hr : IsGLB S r) : ValueDefinable (L := L) O P {r} := by
  let := convexStructure O L
  have hlow := definable_value_bounds O P hF hS false
  have hupp := definable_value_bounds O P hF hlow true
  have he : ({r} : Set O.ValueGroup) = lowerBounds S ∩ upperBounds (lowerBounds S) := by
    ext s
    exact ⟨fun h => (show s = r from h) ▸ hr,fun h => (show IsGLB S s from h).unique hr⟩
  rw [he]
  exact hlow.inter hupp

include hF in
private theorem definable_value_calculation {r s out : O.ValueGroup}
    (hr : ValueDefinable (L := L) O P {r}) (hs : ValueDefinable (L := L) O P {s})
    (l u : (convexLanguage L).Term (Fin 1 ⊕ Fin 2))
    (law : ∀ (v : Fin 1 → K) (w : Fin 2 → K), O.valuation (w 0) = r → O.valuation (w 1) = s →
      ((letI := convexStructure O L
       O.valuation (l.realize (Sum.elim v w)) = O.valuation (u.realize (Sum.elim v w))) ↔
      O.valuation (v 0) = out)) : ValueDefinable (L := L) O P {out} := by
  let := convexStructure O L
  let J := convexLanguage L
  obtain ⟨φ,hφ⟩ := hr
  obtain ⟨ψ,hψ⟩ := hs
  let eqn := valuationLEFormula F l u ⊓ valuationLEFormula F u l
  refine ⟨Formula.iExs (Fin 2) ((φ.relabel (fun _ => .inr 0) ⊓ ψ.relabel (fun _ => .inr 1))
    ⊓ (J.lhomWithConstants P).onFormula eqn),?_⟩
  ext v
  have left (w : Fin 2 → K) : φ.Realize (Sum.elim v w ∘ fun _ => Sum.inr 0) ↔
      O.valuation (w 0) = r := (Set.ext_iff.mp hφ _).symm
  have right (w : Fin 2 → K) : ψ.Realize (Sum.elim v w ∘ fun _ => Sum.inr 1) ↔
      O.valuation (w 1) = s := (Set.ext_iff.mp hψ _).symm
  simp only [mem_ofPred_eq,Formula.realize_iExs,Formula.realize_inf,Formula.realize_relabel,
    LHom.realize_onFormula,eqn,realize_valuationLEFormula O hF,←le_antisymm_iff,left,right]
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := O.valuation_surjective r
    obtain ⟨b,hb⟩ := O.valuation_surjective s
    exact ⟨![a,b],⟨ha,hb⟩,(law v ![a,b] ha hb).mpr hx⟩
  · rintro ⟨w,⟨ha,hb⟩,he⟩
    exact (law v w ha hb).mp he

private def choiceProduct (a b : Fin 1 ⊕ Fin 2) : (convexLanguage L).Term (Fin 1 ⊕ Fin 2) :=
  F.mul.subst ![.var a,.var b]

include hF in
private theorem choiceProduct_realize (a b : Fin 1 ⊕ Fin 2) (v : Fin 1 ⊕ Fin 2 → K) :
    letI := convexStructure O L
    (choiceProduct (F := F) a b).realize v = v a * v b := by
  let := convexStructure O L
  simp [choiceProduct,Term.realize_subst,hF.mul]

include hF in
/-- Unary choice over the parameters of the pullback, including the case
where the first value interval has endpoint zero. The o-minimal input is
the unary cell description of the induced value sets. A named nontrivial
step handles intervals incident to zero and unbounded intervals. -/
theorem fixed_base_value_choice [DenselyOrdered O.ValueGroup] [NoMaxOrder O.ValueGroup]
    (cells : ∀ S, ValueDefinable (L := L) O P S → ∃ C : Finset (Set O.ValueGroup),
      (∀ T ∈ C, IsUnaryCell T) ∧ S = ⋃ T ∈ C, T)
    (square : ∀ t : O.ValueGroup, ∃ q, q*q = t)
    {step : O.ValueGroup} (hstep : 1 < step) (ds : ValueDefinable (L := L) O P {step})
    (S : Set O.ValueGroup) (hne : S.Nonempty) (hS : ValueDefinable (L := L) O P S) :
    ∃ q ∈ S, ValueDefinable (L := L) O P {q} := by
  let := convexStructure O L
  obtain ⟨r,hr,hrS | ⟨b,hb,hgap⟩⟩ := firstValueInterval_of_cells hne (cells S hS)
  · exact ⟨r,hrS,definable_glb O P hF hS hr⟩
  have dr := definable_glb O P hF hS hr
  have dlo : ValueDefinable (L := L) O P (Ioi r) := by
    have hd := (definable_value_bounds O P hF dr false).compl
    have he : Ioi r = (lowerBounds {r})ᶜ := by simp
    rw [he]
    exact hd
  let B := Ioi r \ S
  have dB : ValueDefinable (L := L) O P B := dlo.inter hS.compl
  let x : Fin 1 ⊕ Fin 2 := .inl 0
  let a : Fin 1 ⊕ Fin 2 := .inr 0
  let z : Fin 1 ⊕ Fin 2 := .inr 1
  have above : ∃ c : O.ValueGroup, r < c ∧ Ioo r c ⊆ S ∧ ValueDefinable (L := L) O P {c} := by
    by_cases hn : B.Nonempty
    · obtain ⟨c,hc,_⟩ := firstValueInterval_of_cells hn (cells B dB)
      have lower : b ∈ lowerBounds B := by
        intro u hu
        exact le_of_not_gt (fun h => hu.2 (hgap ⟨hu.1,h⟩))
      exact ⟨c,hb.trans_le (hc.2 lower),fun u hu => by
        by_contra h
        exact hu.2.not_ge (hc.1 (show u ∈ B from ⟨hu.1,h⟩)),definable_glb O P hF dB hc⟩
    · have tail : Ioi r ⊆ S := fun u hu => by
        by_contra h
        exact hn ⟨u,hu,h⟩
      by_cases rz : r = 0
      · exact ⟨step,rz ▸ zero_lt_one.trans hstep,fun _ h => tail h.1,ds⟩
      · refine ⟨r*step,by simpa using mul_lt_mul_of_pos_left hstep (pos_iff_ne_zero.mpr rz),
          fun _ h => tail h.1,?_⟩
        apply definable_value_calculation O P hF dr ds (.var x) (choiceProduct (F := F) a z)
        intro v w ha hz
        simp [choiceProduct_realize O hF,x,a,z,map_mul,ha,hz]
  obtain ⟨c,hrc,hint,dc⟩ := above
  by_cases rz : r = 0
  · have cp : 0 < c := rz ▸ hrc
    have sp := zero_lt_one.trans hstep
    refine ⟨c / step,hint ⟨rz ▸ div_pos cp sp,((div_lt_iff₀ sp).mpr (by simpa using mul_lt_mul_of_pos_left hstep cp))⟩,?_⟩
    apply definable_value_calculation O P hF ds dc (choiceProduct (F := F) x a) (.var z)
    intro v w ha hz
    simp [choiceProduct_realize O hF,x,a,z,map_mul,ha,hz,eq_div_iff sp.ne']
  · obtain ⟨q,hq⟩ := square (r*c)
    have rp := pos_iff_ne_zero.mpr rz
    have hlow : r < q := by
      by_contra! h
      exact (mul_lt_mul_of_pos_left hrc rp).not_ge (hq ▸ mul_le_mul' h h)
    have high : q < c := by
      by_contra! h
      exact (mul_lt_mul_of_pos_right hrc (rp.trans hrc)).not_ge (hq ▸ mul_le_mul' h h)
    refine ⟨q,hint ⟨hlow,high⟩,?_⟩
    apply definable_value_calculation O P hF dr dc (choiceProduct (F := F) x x) (choiceProduct (F := F) a z)
    intro v w ha hz
    simp only [choiceProduct_realize O hF,x,a,z,Sum.elim_inl,Sum.elim_inr,map_mul,ha,hz,←hq]
    exact ⟨fun h => le_antisymm (le_of_not_gt fun ne =>
        (mul_self_lt_mul_self zero_le ne).ne h.symm) (le_of_not_gt fun ne =>
        (mul_self_lt_mul_self zero_le ne).ne h),fun h => by rw [h]⟩

theorem value_has_square_root [IsRealClosed K] (t : O.ValueGroup) :
    ∃ q, q*q = t := by
  obtain ⟨a,ha⟩ := O.valuation_surjective t
  rcases IsRealClosed.isSquare_or_isSquare_neg a with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact ⟨O.valuation b,by rw [←map_mul,←hb,ha]⟩
  · exact ⟨O.valuation b,by rw [←map_mul,←hb,O.valuation.map_neg,ha]⟩

/-- Remark 3.11 with 3.12 supplied by value choice. Only the unary Holly
and value-cell decompositions, the named step and the ordered field terms
are inputs. Every choice of representative is covered by the same formula. -/
theorem atomic_shape_of_value_cells [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    (hO : IsOrderConvex O) [DenselyOrdered O.ValueGroup] [NoMaxOrder O.ValueGroup]
    {T : OrderedFieldTerms (convexLanguage L)}
    (hT : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) T)
    (cells : ∀ S, ValueDefinable (L := L) O P S → ∃ C : Finset (Set O.ValueGroup),
      (∀ U ∈ C, IsUnaryCell U) ∧ S = ⋃ U ∈ C, U)
    {step : O.ValueGroup} (hstep : 1 < step) (ds : ValueDefinable (L := L) O P {step})
    {A : Set K} (atom : letI := convexStructure O L; AtomicOver {U | P.Definable₁ (convexLanguage L) U} A)
    (hnf : UnaryValuativeSet O A) : IsAtomicShape O A := by
  let := convexStructure O L
  apply atomic_shape_of_value_invariance O hT hO atom hnf
  exact unary_atomic_after_naming_value O hT.toInterpretsFieldTerms atom
    (fixed_base_value_choice O P hT.toInterpretsFieldTerms cells (value_has_square_root O) hstep ds)

end GeneralizedEuler.Section3
