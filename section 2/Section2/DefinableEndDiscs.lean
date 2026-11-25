module

public import Section2.EndDiscs
public import Section2.ValuedFieldFormulas

/-! Fixed-parameter definability of the ends of a valuative interval. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

variable {J : Language} {K : Type*} [Field K] [LinearOrder K] [J.Structure K]
  {F : OrderedFieldTerms J} {A : Set K}

private theorem finCases_one {X : Type*} (x y : X) :
    (Fin.cases x (fun _ => y) : Fin 2 → X) 1 = y := rfl

private def unaryAt {α : Type*} (φ : (J[[A]]).Formula (Fin 1)) (t : (J[[A]]).Term α) :
    (J[[A]]).Formula α := φ.subst (fun _ => t)

omit [Field K] [LinearOrder K] in
private theorem realize_unaryAt {α : Type*} (φ : (J[[A]]).Formula (Fin 1))
    (t : (J[[A]]).Term α) (v : α → K) :
    (unaryAt φ t).Realize v ↔ φ.Realize (fun _ => t.realize v) :=
  BoundedFormula.realize_subst

private def namedSub {α : Type*} (F : OrderedFieldTerms J)
    (x y : (J[[A]]).Term α) : (J[[A]]).Term α :=
  ((J.lhomWithConstants A).onTerm F.sub).subst (Fin.cases x (fun _ => y))

private theorem realize_namedSub {α : Type*} (hF : InterpretsOrderedFieldTerms (A := K) F)
    (x y : (J[[A]]).Term α) (v : α → K) :
    (namedSub F x y).realize v = x.realize v - y.realize v := by
  simp only [namedSub, Term.realize_subst, LHom.realize_onTerm, hF.sub,
    Fin.cases_zero, finCases_one]

private def namedOrder {α : Type*} (F : OrderedFieldTerms J)
    (x y : (J[[A]]).Term α) : (J[[A]]).Formula α :=
  ((J.lhomWithConstants A).onRelation F.le).formula (Fin.cases x (fun _ => y))

private theorem realize_namedOrder {α : Type*} (hF : InterpretsOrderedFieldTerms (A := K) F)
    (x y : (J[[A]]).Term α) (v : α → K) :
    (namedOrder F x y).Realize v ↔ x.realize v ≤ y.realize v := by
  simp only [namedOrder, Formula.realize_rel, LHom.map_onRelation, hF.le,
    Fin.cases_zero, finCases_one]

private noncomputable def unaryProjection (F : OrderedFieldTerms J) (reverse : Bool)
    (φ : (J[[A]]).Formula (Fin 1)) : (J[[A]]).Formula (Fin 1) :=
  let x : (J[[A]]).Term (Fin 1 ⊕ Unit) := .var (.inl 0)
  let y : (J[[A]]).Term (Fin 1 ⊕ Unit) := .var (.inr ())
  let le := if reverse then namedOrder F x y else namedOrder F y x
  Formula.iExs Unit (unaryAt φ y ⊓ le)

private theorem definable₁_ray (hF : InterpretsOrderedFieldTerms (A := K) F)
    {U : Set K} (hU : A.Definable₁ J U) (reverse : Bool) :
    A.Definable₁ J {x | ∃ y ∈ U, if reverse then x ≤ y else y ≤ x} := by
  obtain ⟨φ, hφ⟩ := hU
  refine ⟨unaryProjection F reverse φ, ?_⟩
  ext v
  have hval (y : K) : φ.Realize (fun _ => y) ↔ y ∈ U :=
    (Set.ext_iff.mp hφ (fun _ => y)).symm
  cases reverse <;>
    simp only [unaryProjection, Bool.false_eq_true, ↓reduceIte, Formula.realize_iExs,
      Formula.realize_inf, realize_unaryAt, realize_namedOrder hF,
      Term.realize_var, Sum.elim_inr, Sum.elim_inl, hval, Set.mem_ofPred]
  all_goals
    exact ⟨fun ⟨y, hy, h⟩ => ⟨fun _ => y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y (), hy, h⟩⟩

omit [Field K] [LinearOrder K] in
private theorem definable₁_compl {U : Set K} (hU : A.Definable₁ J U) :
    A.Definable₁ J Uᶜ := hU.compl

private theorem realizable_endClass (hF : InterpretsOrderedFieldTerms (A := K) F)
    {U : Set K} (hU : A.Definable₁ J U) (reverse : Bool) :
    A.Definable₁ J {x | x ∈ U ∧
      ∀ y ∈ U, (if reverse then y ≤ x else x ≤ y) ∨ rayPeriod U (x - y)} := by
  obtain ⟨φ, hφ⟩ := hU
  let x : (J[[A]]).Term (Fin 1 ⊕ Unit) := .var (.inl 0)
  let y : (J[[A]]).Term (Fin 1 ⊕ Unit) := .var (.inr ())
  let z : (J[[A]]).Term ((Fin 1 ⊕ Unit) ⊕ Unit) := .var (.inr ())
  let lift := Term.relabel (L := J[[A]]) (Sum.inl : Fin 1 ⊕ Unit → (Fin 1 ⊕ Unit) ⊕ Unit)
  let translated := namedSub F z (namedSub F (lift y) (lift x))
  let period := Formula.iAlls Unit ((unaryAt φ z).iff (unaryAt φ translated))
  let order := if reverse then namedOrder F y x else namedOrder F x y
  refine ⟨φ ⊓ Formula.iAlls Unit ((unaryAt φ y).imp (order ⊔ period)), ?_⟩
  ext v
  have hval (q : Fin 1 → K) : φ.Realize q ↔ q 0 ∈ U := (Set.ext_iff.mp hφ q).symm
  have horder (s : Unit → K) :
      order.Realize (Sum.elim v s) ↔ if reverse then s () ≤ v 0 else v 0 ≤ s () := by
    cases reverse <;> simp [order, realize_namedOrder hF, x, y]
  have hperiod (s : Unit → K) :
      period.Realize (Sum.elim v s) ↔ rayPeriod U (v 0 - s ()) := by
    simp only [period, Formula.realize_iAlls, Formula.realize_iff, realize_unaryAt,
      translated, realize_namedSub hF, lift, Term.realize_relabel, x, y, z, Term.realize_var,
      Function.comp_apply, Sum.elim_inl, Sum.elim_inr, hval, sub_sub_eq_add_sub]
    constructor
    · intro h a
      simpa [add_sub_assoc] using h (fun _ => a)
    · intro h a
      simpa [add_sub_assoc] using h (a ())
  simp only [Set.mem_ofPred, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, hval, realize_unaryAt, y, Term.realize_var, Sum.elim_inr, horder, hperiod]
  refine and_congr_right fun _ => ?_
  exact ⟨fun h s hs => h (s ()) hs, fun h s hs => h (fun _ => s) hs⟩

variable [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO in
theorem definable₁_leftEndDisc (hF : InterpretsOrderedFieldTerms (A := K) F)
    {e : ValuativeIntervalEnd (K := K)} {hi : Option (ValuativeIntervalEnd (K := K))}
    (hd : IsEndDisc O e.disc) (hne : (valuativeInterval (some e) hi).Nonempty)
    (h : A.Definable₁ J (valuativeInterval (some e) hi)) : A.Definable₁ J e.disc := by
  obtain ⟨D, b⟩ := e
  have hRay : A.Definable₁ J {x | allowedAbove (some ⟨D, b⟩) x} := by
    rw [← upperClosure_valuativeInterval hne]
    exact definable₁_ray hF h false
  cases b
  · have hCompl : {x | allowedAbove (some ⟨D, false⟩) x}ᶜ = {x | ∃ y ∈ D, x ≤ y} := by
      ext x
      simp [allowedAbove, not_lt]
    have h := definable₁_compl hRay
    rw [hCompl] at h
    have hend := realizable_endClass hF h true
    change A.Definable₁ J (lowerEndClass (A := Kᵒᵈ) {x | ∃ y ∈ D, (show K from x) ≤ y}) at hend
    rwa [IsEndDisc.eq_lowerEndClass_lowerRay O hO hd] at hend
  · have hend := realizable_endClass hF hRay false
    change A.Definable₁ J (lowerEndClass {x | ∃ y ∈ D, y ≤ x}) at hend
    rwa [IsEndDisc.eq_lowerEndClass_upperRay O hO hd] at hend

include hO in
theorem definable₁_rightEndDisc (hF : InterpretsOrderedFieldTerms (A := K) F)
    {lo : Option (ValuativeIntervalEnd (K := K))} {e : ValuativeIntervalEnd (K := K)}
    (hd : IsEndDisc O e.disc) (hne : (valuativeInterval lo (some e)).Nonempty)
    (h : A.Definable₁ J (valuativeInterval lo (some e))) : A.Definable₁ J e.disc := by
  obtain ⟨D, b⟩ := e
  have hRay : A.Definable₁ J {x | allowedBelow (some ⟨D, b⟩) x} := by
    rw [← lowerClosure_valuativeInterval hne]
    exact definable₁_ray hF h true
  cases b
  · have hCompl : {x | allowedBelow (some ⟨D, false⟩) x}ᶜ = {x | ∃ y ∈ D, y ≤ x} := by
      ext x
      simp [allowedBelow, not_lt]
    have h := definable₁_compl hRay
    rw [hCompl] at h
    have hend := realizable_endClass hF h false
    change A.Definable₁ J (lowerEndClass {x | ∃ y ∈ D, y ≤ x}) at hend
    rwa [IsEndDisc.eq_lowerEndClass_upperRay O hO hd] at hend
  · have hend := realizable_endClass hF hRay true
    change A.Definable₁ J (lowerEndClass (A := Kᵒᵈ) {x | ∃ y ∈ D, (show K from x) ≤ y}) at hend
    rwa [IsEndDisc.eq_lowerEndClass_lowerRay O hO hd] at hend

omit [IsStrictOrderedRing K] in
theorem definable₁_valuativeInterval_of_ends (hF : InterpretsOrderedFieldTerms (A := K) F)
    (lo hi : Option (ValuativeIntervalEnd (K := K)))
    (hlo : ∀ e ∈ lo, A.Definable₁ J e.disc) (hhi : ∀ e ∈ hi, A.Definable₁ J e.disc) :
    A.Definable₁ J (valuativeInterval lo hi) := by
  have hleft : A.Definable₁ J {x | allowedAbove lo x} := by
    rcases lo with _ | ⟨D, b⟩
    · exact Set.definable_univ
    have hD := hlo ⟨D, b⟩ rfl
    cases b
    · have h := definable₁_compl (definable₁_ray hF hD true)
      convert h using 1
      ext x
      simp [allowedAbove, not_le]
    · exact definable₁_ray hF hD false
  have hright : A.Definable₁ J {x | allowedBelow hi x} := by
    rcases hi with _ | ⟨D, b⟩
    · exact Set.definable_univ
    have hD := hhi ⟨D, b⟩ rfl
    cases b
    · have h := definable₁_compl (definable₁_ray hF hD false)
      convert h using 1
      ext x
      simp [allowedBelow, not_le]
    · exact definable₁_ray hF hD true
  exact hleft.inter hright

include hO in
theorem definable₁_valuativeInterval_iff_ends (hF : InterpretsOrderedFieldTerms (A := K) F)
    {lo hi : Option (ValuativeIntervalEnd (K := K))} (hne : (valuativeInterval lo hi).Nonempty)
    (hlo : ∀ e ∈ lo, IsEndDisc O e.disc) (hhi : ∀ e ∈ hi, IsEndDisc O e.disc) :
    A.Definable₁ J (valuativeInterval lo hi) ↔
      (∀ e ∈ lo, A.Definable₁ J e.disc) ∧ (∀ e ∈ hi, A.Definable₁ J e.disc) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => definable₁_valuativeInterval_of_ends hF lo hi h.1 h.2⟩
  · intro e he
    have hd := hlo e he
    have he' : lo = some e := by simpa using he
    subst lo
    exact definable₁_leftEndDisc O hO hF hd hne h
  · intro e he
    have hd := hhi e he
    have he' : hi = some e := by simpa using he
    subst hi
    exact definable₁_rightEndDisc O hO hF hd hne h

end GeneralizedEuler.Section2
