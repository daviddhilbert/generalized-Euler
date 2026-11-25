module

public import Section3.ValueChoice

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [Field K] {L : Language} [L.Structure K] (O : ValuationSubring K)
  (P : Set K) {F : FieldTerms (convexLanguage L)}
  (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
  {n : ℕ}

def AtValueTuple (r : O.ValueGroup) (D : Set (Fin n → K)) : Prop :=
  letI := convexStructure O L
  ∃ φ : ((convexLanguage L)[[P]]).Formula (Fin n ⊕ Unit), ∀ x w, O.valuation w = r →
    (φ.Realize (Sum.elim x (fun _ => w)) ↔ x ∈ D)

private noncomputable def saturateValue (φ : ((convexLanguage L)[[P]]).Formula (Fin n ⊕ Unit)) :
    ((convexLanguage L)[[P]]).Formula (Fin n ⊕ Unit) :=
  let J := convexLanguage L
  let r : J.Term ((Fin n ⊕ Unit) ⊕ Unit) := .var (.inl (.inr ()))
  let w : J.Term ((Fin n ⊕ Unit) ⊕ Unit) := .var (.inr ())
  let cmp := valuationLEFormula F r w ⊓ valuationLEFormula F w r
  Formula.iExs Unit ((J.lhomWithConstants P).onFormula cmp ⊓
    φ.relabel (Sum.elim (fun j => .inl (.inl j)) (fun _ => .inr ())))

include hF in
private theorem saturateValue_correct (φ : ((convexLanguage L)[[P]]).Formula (Fin n ⊕ Unit))
    (a : Fin n → K) (v : K) : letI := convexStructure O L
    (saturateValue (F := F) P φ).Realize (Sum.elim a (fun _ => v)) ↔
    ∃ w, O.valuation w = O.valuation v ∧ φ.Realize (Sum.elim a (fun _ => w)) := by
  let := convexStructure O L
  simp only [saturateValue,Formula.realize_iExs,Formula.realize_inf,LHom.realize_onFormula,
    realize_valuationLEFormula O hF,Term.realize_var,Sum.elim_inl,Sum.elim_inr,←le_antisymm_iff,
    Formula.realize_relabel]
  have eqv (s : Unit → K) :
      Sum.elim (Sum.elim a (fun _ : Unit => v)) s ∘
        Sum.elim (fun j => Sum.inl (Sum.inl j)) (fun _ : Unit => Sum.inr ()) =
        Sum.elim a (fun _ : Unit => s ()) := by funext i; cases i <;> rfl
  exact ⟨fun ⟨s,he,hm⟩ => ⟨s (),he.symm,eqv s ▸ hm⟩,
    fun ⟨w,he,hm⟩ => ⟨fun _ => w,he.symm,(eqv (fun _ => w)).symm ▸ hm⟩⟩

/-- Test a represented value by quantifying a tuple in A on which a given
formula (or its negation) holds. -/
private noncomputable def meetsTuple (φ : ((convexLanguage L)[[P]]).Formula (Fin n ⊕ Unit))
    (A : ((convexLanguage L)[[P]]).Formula (Fin n)) : ((convexLanguage L)[[P]]).Formula (Fin 1) :=
  Formula.iExs (Fin n) (A.relabel Sum.inr ⊓ φ.relabel (Sum.elim Sum.inr (fun _ => .inl 0)))

private theorem meetsTuple_correct (φ : ((convexLanguage L)[[P]]).Formula (Fin n ⊕ Unit))
    (A : ((convexLanguage L)[[P]]).Formula (Fin n)) (v : Fin 1 → K) :
    letI := convexStructure O L
    (meetsTuple P φ A).Realize v ↔ ∃ x, A.Realize x ∧ φ.Realize (Sum.elim x (fun _ => v 0)) := by
  let := convexStructure O L
  simp only [meetsTuple,Formula.realize_iExs,Formula.realize_inf,Formula.realize_relabel]
  apply exists_congr
  intro w
  have h : Sum.elim v w ∘ Sum.elim Sum.inr (fun _ : Unit => .inl 0) =
    Sum.elim w (fun _ : Unit => v 0) := by funext i; cases i <;> rfl
  rw [h]
  rfl

include hF in
/-- The first assertion of 3.12 for field tuples of arbitrary arity. A
single value variable suffices, since the assertion can be applied again
over the enlarged base. The exceptional-value predicate is defined from
two independently quantified tuples and is invariant on representatives. -/
theorem tuple_atomic_after_naming_value [DenselyOrdered O.ValueGroup] [NoMaxOrder O.ValueGroup]
    [IsRealClosed K] (cells : ∀ S, ValueDefinable (L := L) O P S → ∃ C : Finset (Set O.ValueGroup),
      (∀ T ∈ C, IsUnaryCell T) ∧ S = ⋃ T ∈ C, T)
    {step : O.ValueGroup} (hs : 1 < step) (ds : ValueDefinable (L := L) O P {step})
    {A : Set (Fin n → K)} (atom : letI := convexStructure O L
      AtomicOver {D | P.Definable (convexLanguage L) D} A)
    (r : O.ValueGroup) : AtomicOver {D | AtValueTuple (L := L) O P r D} A := by
  let := convexStructure O L
  obtain ⟨α,hα⟩ := atom.1
  have hA (a : Fin n → K) : α.Realize a ↔ a ∈ A := (Set.ext_iff.mp hα a).symm
  refine ⟨⟨α.relabel Sum.inl,fun x w _ => ?_⟩,atom.2.nonempty,?_⟩
  · rw [Formula.realize_relabel]; exact hA x
  rintro D ⟨φ,hφ⟩
  let sec (s : O.ValueGroup) := {a : Fin n → K | ∃ w, O.valuation w = s ∧ φ.Realize (Sum.elim a (fun _ => w))}
  let bad := {s | (A ∩ sec s).Nonempty ∧ (A \ sec s).Nonempty}
  let ψ := saturateValue (F := F) P φ
  have eval (a : Fin n → K) (w : K) : ψ.Realize (Sum.elim a (fun _ => w)) ↔
      a ∈ sec (O.valuation w) := saturateValue_correct O P hF φ a w
  have db : ValueDefinable (L := L) O P bad := by
    refine ⟨meetsTuple P ψ α ⊓ meetsTuple P ψ.not α,?_⟩
    ext v
    simp only [mem_ofPred_eq,Formula.realize_inf,meetsTuple_correct,Formula.realize_not,eval,hA]
    rfl
  have good : ¬ bad.Nonempty := by
    intro nonempty
    obtain ⟨s,bads,defS⟩ := fixed_base_value_choice O P hF cells (value_has_square_root O) hs ds bad nonempty db
    obtain ⟨σ,hσ⟩ := defS
    have defSec : P.Definable (convexLanguage L) (sec s) := by
      refine ⟨Formula.iExs Unit (φ ⊓ σ.relabel (fun _ => .inr ())),?_⟩
      ext v
      have ev (w : Unit → K) : σ.Realize (Sum.elim v w ∘ fun _ => Sum.inr ()) ↔ O.valuation (w ()) = s :=
        (Set.ext_iff.mp hσ _).symm
      simp only [mem_ofPred_eq,Formula.realize_iExs,Formula.realize_inf,Formula.realize_relabel,ev]
      refine ⟨fun ⟨w,hw,hv⟩ => ⟨fun _ => w,hv,hw⟩,fun ⟨w,hv,hw⟩ => ⟨w (),hw,?_⟩⟩
      exact hv
    obtain ⟨⟨x,hx,hxt⟩,y,hy,hyt⟩ := bads
    exact hyt ((atom.2.uniform _ defSec x hx y hy).mp hxt)
  have eqD : sec r = D := by
    ext x
    refine ⟨fun ⟨w,hw,hm⟩ => (hφ x w hw).mp hm,?_⟩
    intro h
    obtain ⟨w,hw⟩ := O.valuation_surjective r
    exact ⟨w,hw,(hφ x w hw).mpr h⟩
  intro x hx y hy
  rw [←eqD]
  constructor <;> intro h <;> by_contra ne
  · exact good ⟨r,⟨x,hx,h⟩,y,hy,ne⟩
  · exact good ⟨r,⟨y,hy,h⟩,x,hx,ne⟩

end GeneralizedEuler.Section3
