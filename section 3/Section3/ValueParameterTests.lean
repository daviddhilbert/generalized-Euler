module

public import Section3.AtomicShapes
public import Section3.AtomicParameters

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {L : Language} {K : Type*} [Field K] [L.Structure K]
  (O : ValuationSubring K)

/-- A unary set defined over P and one value. The second field variable
represents the value. The formula must work for every representative. -/
def AtValue (P : Set K) (r : O.ValueGroup) (D : Set K) : Prop :=
  letI := convexStructure O L
  ∃ φ : ((convexLanguage L)[[P]]).Formula (Fin 2), ∀ x w : K,
    O.valuation w = r → (φ.Realize ![x,w] ↔ x ∈ D)

variable {P D : Set K}

theorem atValue_base (hD : letI := convexStructure O L; P.Definable₁ (convexLanguage L) D)
    (r : O.ValueGroup) : AtValue (L := L) O P r D := by
  let := convexStructure O L
  obtain ⟨φ,hφ⟩ := hD
  refine ⟨φ.relabel (fun _ => 0),fun x w _ => ?_⟩
  rw [Formula.realize_relabel]
  exact (Set.ext_iff.mp hφ (fun _ => x)).symm

variable {F : OrderedFieldTerms (convexLanguage L)} [LinearOrder K]
variable (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
include hF

theorem atValue_valuation_fiber (r : O.ValueGroup) :
    AtValue (L := L) O P r {x | O.valuation x = r} := by
  let := convexStructure O L
  let J := convexLanguage L
  let x : J.Term (Fin 2) := .var 0
  let w : J.Term (Fin 2) := .var 1
  let φ := valuationLEFormula F.toFieldTerms x w ⊓ valuationLEFormula F.toFieldTerms w x
  refine ⟨(J.lhomWithConstants P).onFormula φ,?_⟩
  intro a b hb
  rw [LHom.realize_onFormula]
  simp only [φ,Formula.realize_inf,realize_valuationLEFormula O hF.toInterpretsFieldTerms,
    x,w,Term.realize_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    hb, Set.mem_ofPred_eq,le_antisymm_iff]

theorem atValue_open_thickening
    (hD : letI := convexStructure O L; P.Definable₁ (convexLanguage L) D) (r : O.ValueGroup) :
    AtValue (L := L) O P r {x | ∃ a ∈ D, x ∈ openDisc O a r} := by
  let := convexStructure O L
  let J := convexLanguage L
  obtain ⟨φ,hφ⟩ := hD
  let x : J.Term (Fin 2 ⊕ Unit) := .var (.inl 0)
  let w : J.Term (Fin 2 ⊕ Unit) := .var (.inl 1)
  let a : J.Term (Fin 2 ⊕ Unit) := .var (.inr ())
  let ψ := discMemberFormula F.toFieldTerms false x a w
  refine ⟨Formula.iExs Unit (φ.relabel (fun _ => .inr ()) ⊓
    (J.lhomWithConstants P).onFormula ψ),?_⟩
  intro b c hc
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_relabel,
    LHom.realize_onFormula, ψ,realize_discMemberFormula O hF.toInterpretsFieldTerms,
    Bool.false_eq_true,ite_false,x,a,w,Term.realize_var,Sum.elim_inl,Sum.elim_inr,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,hc,mem_ofPred_eq]
  constructor
  · rintro ⟨v,hv,ht⟩
    exact ⟨v (), (Set.ext_iff.mp hφ (fun _ => v ())).mpr hv,ht⟩
  · rintro ⟨z,hz,ht⟩
    exact ⟨fun _ => z,(Set.ext_iff.mp hφ (fun _ => z)).mp hz,ht⟩

/-- The midpoint cut 2x < y+z is equivalently x-y < z-x, so it only
needs the field subtraction term and the order relation. -/
theorem definable_midpoint_cut {R : Set K} [IsStrictOrderedRing K]
    (hD : letI := convexStructure O L; P.Definable₁ (convexLanguage L) D)
    (hR : letI := convexStructure O L; P.Definable₁ (convexLanguage L) R) :
    letI := convexStructure O L
    P.Definable₁ (convexLanguage L) {x | ∃ y ∈ D, ∃ z ∈ R, 2*x < y+z} := by
  let := convexStructure O L
  let J := convexLanguage L
  obtain ⟨φ,hφ⟩ := hD
  obtain ⟨ψ,hψ⟩ := hR
  let x : J.Term (Fin 1 ⊕ Fin 2) := .var (.inl 0)
  let y : J.Term (Fin 1 ⊕ Fin 2) := .var (.inr 0)
  let z : J.Term (Fin 1 ⊕ Fin 2) := .var (.inr 1)
  let sub (a b : J.Term (Fin 1 ⊕ Fin 2)) := F.sub.subst ![a,b]
  let cut := (F.le.formula ![sub z x,sub x y]).not
  refine ⟨Formula.iExs (Fin 2) (φ.relabel (fun _ => .inr 0) ⊓ ψ.relabel (fun _ => .inr 1)
    ⊓ (J.lhomWithConstants P).onFormula cut),?_⟩
  ext v
  change (∃ a ∈ D, ∃ b ∈ R, 2*v 0 < a+b) ↔ _
  rw [Set.mem_ofPred_eq, Formula.realize_iExs]
  have eval (s : Fin 2 → K) : cut.Realize (Sum.elim v s) ↔ 2*v 0 < s 0+s 1 := by
    simp [cut,sub,Formula.realize_rel,hF.le,hF.sub,x,y,z,Matrix.cons_val_fin_one]
    constructor <;> intro h <;> linarith
  simp only [Formula.realize_inf,LHom.realize_onFormula,eval,Formula.realize_relabel]
  constructor
  · rintro ⟨a,ha,b,hb,ht⟩
    exact ⟨![a,b],⟨(Set.ext_iff.mp hφ (fun _ => a)).mp ha,
      (Set.ext_iff.mp hψ (fun _ => b)).mp hb⟩,ht⟩
  · rintro ⟨s,⟨ha,hb⟩,ht⟩
    exact ⟨s 0,(Set.ext_iff.mp hφ (fun _ => s 0)).mpr ha,s 1,
      (Set.ext_iff.mp hψ (fun _ => s 1)).mpr hb,ht⟩

/-- The four forms of 3.11 over a fixed base, using 3.12 once for each
named radius. The only field element representing that radius is a free
variable in the defining formula, never a named parameter. -/
theorem atomic_shape_of_value_invariance [IsStrictOrderedRing K] (hO : IsOrderConvex O)
    [DenselyOrdered O.ValueGroup] [NoMaxOrder O.ValueGroup] {U : Set K}
    (atom : letI := convexStructure O L; AtomicOver {D | P.Definable₁ (convexLanguage L) D} U)
    (hnf : UnaryValuativeSet O U)
    (named : ∀ r, GeneratesType {D | AtValue (L := L) O P r D} U) :
    IsAtomicShape O U := by
  let := convexStructure O L
  obtain ⟨pieces,hpieces,_⟩ := existsUnique_hollyDecomposition O hO hnf
  let tests : Set (Set K) := {D | ∃ r, AtValue (L := L) O P r D}
  have uniform : GeneratesType tests U := by
    refine ⟨atom.2.nonempty,?_⟩
    rintro D ⟨r,hr⟩
    exact (named r).uniform D hr
  have base (D : Set K) (hd : P.Definable₁ (convexLanguage L) D) : D ∈ tests :=
    ⟨1,atValue_base O hd 1⟩
  exact atomic_shape_of_holly O hO hF atom hpieces tests uniform base
    (fun r => ⟨r,atValue_valuation_fiber O hF r⟩)
    (fun _ _ hl hr => base _ (definable_midpoint_cut O hF hl hr))
    (fun _ hd r => ⟨r,atValue_open_thickening O hF hd r⟩)

end GeneralizedEuler.Section3
