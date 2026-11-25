module

public import Section3.ValueParameterTests
import all Section3.ValueParameterTests

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} {J : Language} [J.Structure K] {P A : Set K}

private theorem definable_section_exists {D : Set (K × K)} (hd : P.Definable₂ J D)
    (ha : P.Definable₁ J A) (swap : Bool) :
    P.Definable₁ J {x | ∃ z ∈ A, (if swap then (z,x) else (x,z)) ∈ D} := by
  obtain ⟨φ,hφ⟩ := hd
  obtain ⟨ψ,hψ⟩ := ha
  let x : Fin 1 ⊕ Unit := .inl 0
  let z : Fin 1 ⊕ Unit := .inr ()
  let pair := if swap then ![z,x] else ![x,z]
  refine ⟨Formula.iExs Unit (ψ.relabel (fun _ => z) ⊓ φ.relabel pair),?_⟩
  ext v
  have hD (s : Unit → K) : φ.Realize (Sum.elim v s ∘ pair) ↔
      (if swap then (s (),v 0) else (v 0,s ())) ∈ D := by
    cases swap <;> exact (Set.ext_iff.mp hφ _).symm
  have hA (s : Unit → K) : ψ.Realize (Sum.elim v s ∘ fun _ => z) ↔ s () ∈ A :=
    (Set.ext_iff.mp hψ _).symm
  simp only [mem_ofPred_eq,Formula.realize_iExs,Formula.realize_inf,Formula.realize_relabel,hA,hD]
  exact ⟨fun ⟨a,ha,he⟩ => ⟨fun _ => a,ha,he⟩,fun ⟨s,hs,he⟩ => ⟨s (),hs,he⟩⟩

variable {L : Language} [Field K] [L.Structure K] (O : ValuationSubring K)

private def valueRelation (D : Set (K × K)) : Set (K × K) :=
  {p | ∃ w, O.valuation w = O.valuation p.2 ∧ (p.1,w) ∈ D}

/-- Saturate a field formula in its second coordinate under equality of
valuation. Its sections now use a value parameter at every radius. -/
private theorem definable_valueRelation {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) {D : Set (K × K)}
    (hd : letI := convexStructure O L; P.Definable₂ (convexLanguage L) D) :
    letI := convexStructure O L
    P.Definable₂ (convexLanguage L) (valueRelation O D) := by
  let := convexStructure O L
  let J := convexLanguage L
  obtain ⟨φ,hφ⟩ := hd
  let x : Fin 2 ⊕ Unit := .inl 0
  let r : J.Term (Fin 2 ⊕ Unit) := .var (.inl 1)
  let w : J.Term (Fin 2 ⊕ Unit) := .var (.inr ())
  let eqv := valuationLEFormula F w r ⊓ valuationLEFormula F r w
  refine ⟨Formula.iExs Unit ((J.lhomWithConstants P).onFormula eqv ⊓ φ.relabel ![x,.inr ()]),?_⟩
  ext v
  have hD (s : Unit → K) : φ.Realize (Sum.elim v s ∘ ![x,.inr ()]) ↔ (v 0,s ()) ∈ D :=
    (Set.ext_iff.mp hφ _).symm
  change (∃ w, O.valuation w = O.valuation (v 1) ∧ (v 0,w) ∈ D) ↔ _
  simp only [mem_ofPred_eq,Formula.realize_iExs,Formula.realize_inf,LHom.realize_onFormula,
    eqv,realize_valuationLEFormula O hF,r,w,Term.realize_var,Sum.elim_inl,Sum.elim_inr,
    Formula.realize_relabel,hD,←le_antisymm_iff]
  exact ⟨fun ⟨u,hu,he⟩ => ⟨fun _ => u,hu,he⟩,fun ⟨s,hs,he⟩ => ⟨s (),hs,he⟩⟩

/-- The first assertion of 3.12 for an arbitrary finite tuple of field
coordinates can be viewed as a choice argument on *one* value variable:
a value that splits an atom would give a base-definable splitting value.
Here it is specialized to unary atoms for Remark 3.11. -/
theorem unary_atomic_after_naming_value {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (atom : letI := convexStructure O L; AtomicOver {D | P.Definable₁ (convexLanguage L) D} A)
    (choice : ∀ S : Set O.ValueGroup, S.Nonempty →
      (letI := convexStructure O L; P.Definable₁ (convexLanguage L) (O.valuation ⁻¹' S)) →
      ∃ r ∈ S, letI := convexStructure O L
               P.Definable₁ (convexLanguage L) {w | O.valuation w = r})
    (r : O.ValueGroup) : GeneratesType {D | AtValue (L := L) O P r D} A := by
  let := convexStructure O L
  let J := convexLanguage L
  refine ⟨atom.2.nonempty,?_⟩
  rintro D ⟨φ,hφ⟩
  let R := {p : K × K | φ.Realize ![p.1,p.2]}
  have dR : P.Definable₂ J R := by
    refine ⟨φ,?_⟩
    ext v
    change φ.Realize ![v 0,v 1] ↔ φ.Realize v
    rw [show ![v 0,v 1] = v from funext fun i => by fin_cases i <;> rfl]
  let Q := valueRelation O R
  have dQ := definable_valueRelation O hF dR
  let sec (s : O.ValueGroup) := {x : K | ∃ w, O.valuation w = s ∧ (x,w) ∈ R}
  let bad := {s | (A ∩ sec s).Nonempty ∧ (A \ sec s).Nonempty}
  have badDef : P.Definable₁ J (O.valuation ⁻¹' bad) := by
    exact (definable_section_exists dQ atom.1 true).inter
      (definable_section_exists (D := Qᶜ) dQ.compl atom.1 true)
  have none : ¬ bad.Nonempty := by
    intro hn
    obtain ⟨s,hs,defS⟩ := choice bad hn badDef
    have defSec : P.Definable₁ J (sec s) := by
      have h := definable_section_exists dQ defS false
      have eqn : {x : K | ∃ z ∈ {w | O.valuation w = s}, (x,z) ∈ Q} = sec s := by
        ext x
        constructor
        · rintro ⟨z,hz,w,hw,hm⟩
          exact ⟨w,hw.trans hz,hm⟩
        · rintro ⟨w,hw,hm⟩
          exact ⟨w,hw,w,rfl,hm⟩
      rwa [←eqn]
    obtain ⟨⟨x,hx,hm⟩,y,hy,hn⟩ := hs
    exact hn ((atom.2.uniform _ defSec x hx y hy).mp hm)
  have eqD : sec r = D := by
    ext x
    refine ⟨fun ⟨w,hw,hm⟩ => (hφ x w hw).mp hm,?_⟩
    intro hx
    obtain ⟨w,hw⟩ := O.valuation_surjective r
    exact ⟨w,hw,(hφ x w hw).mpr hx⟩
  intro x hx y hy
  rw [←eqD]
  constructor <;> intro h <;> by_contra hn
  · exact none ⟨r,⟨x,hx,h⟩,y,hy,hn⟩
  · exact none ⟨r,⟨y,hy,h⟩,x,hx,hn⟩

end GeneralizedEuler.Section3
