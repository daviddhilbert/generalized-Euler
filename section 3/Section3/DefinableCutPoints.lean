module

public import Section3.FixedHolly
public import Section3.CutDiscPoints
public import Section2.ValuedFieldFormulas
import all Section2.DiscCodes

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [Field K] {L : Language} [L.Structure K] (O : ValuationSubring K)
    [DenselyOrdered O.ValueGroup] {P : Set K}

/-- The closed parent of a definable open disc is definable over the
same parameters. Intersect all closed discs containing the open disc.
Its center and a representative of its radius only enter the verification. -/
theorem definable_closed_parent {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) {c : K}
    {r : O.ValueGroup} (hr : r ≠ 0) :
    letI := convexStructure O L
    P.Definable₁ (convexLanguage L) (openDisc O c r) →
      P.Definable₁ (convexLanguage L) (closedDisc O c r) := by
  let := convexStructure O L
  rintro ⟨φ,hφ⟩
  let J := convexLanguage L
  let D := Fin 1 ⊕ Fin 2
  let x : D := .inl 0
  let a : D := .inr 0
  let b : D := .inr 1
  let ball {S : Type} (j l m : S) : (J[[P]]).Formula S :=
    (J.lhomWithConstants P).onFormula (discMemberFormula F true (.var j) (.var l) (.var m))
  have eval {S : Type} (j l m : S) (v : S → K) :
      (ball j l m).Realize v ↔ v j ∈ closedDisc O (v l) (O.valuation (v m)) := by
    simp only [ball,LHom.realize_onFormula,realize_discMemberFormula O hF,ite_true,Term.realize_var]
  let pred := φ.relabel (fun _ => (Sum.inr () : D ⊕ Unit))
  let contains := Formula.iAlls Unit (pred.imp (ball (.inr ()) (.inl a) (.inl b)))
  refine ⟨Formula.iAlls (Fin 2) (contains.imp (ball x a b)),?_⟩
  ext v
  have obs (u : K) : φ.Realize (fun _ => u) ↔ u ∈ openDisc O c r := (Set.ext_iff.mp hφ _).symm
  have inner (w : Fin 2 → K) : contains.Realize (Sum.elim v w) ↔
      openDisc O c r ⊆ closedDisc O (w 0) (O.valuation (w 1)) := by
    simp only [contains,Formula.realize_iAlls,Formula.realize_imp,pred,Formula.realize_relabel,eval,
      Function.comp_def,Sum.elim_inr,Sum.elim_inl,obs,a,b]
    exact ⟨fun H u => H (fun _ => u),fun H _ h => H h⟩
  change v 0 ∈ closedDisc O c r ↔ _
  rw [mem_ofPred_eq,Formula.realize_iAlls]
  constructor
  · intro h w
    rw [Formula.realize_imp,inner,eval]
    exact fun sub => closedDisc_minimal_parent O hr sub h
  · intro H
    obtain ⟨d,hd⟩ := O.valuation_surjective r
    have result := H ![c,d]
    rw [Formula.realize_imp,inner,eval] at result
    change (openDisc O c r ⊆ closedDisc O c (O.valuation d) → v 0 ∈ closedDisc O c (O.valuation d)) at result
    rw [hd] at result
    exact result (fun x h => (show O.valuation (x-c) < r from h).le)

variable [LinearOrder K] [IsStrictOrderedRing K] (hO : IsOrderConvex O)

include hO in
/-- Corollary 3.21 from HNF and 3.20 in the valued-field presentation
over a fixed parameter set. All components, their individual ends and
the closed parents used in applying 3.20 are defined over this base. -/
theorem cut_point_of_holly_and_closed_points {F : OrderedFieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
    (A base : Set K) (d : DiscCode O) (pieces : Finset (Set K)) (hnf : IsHollyDecomposition O A pieces) :
    letI := convexStructure O L
    P.Definable₁ (convexLanguage L) A →
    (∀ a r, P.Definable₁ (convexLanguage L) (closedDisc O a r) → (base ∩ closedDisc O a r).Nonempty) →
    ((d.points O) ∩ A).Nonempty → ((d.points O) \ A).Nonempty → (base ∩ d.points O).Nonempty := by
  classical
  let := convexStructure O L
  intro hd closed meets misses
  have forms (i : pieces) := (hnf.1 i.val i.property).2
  choose lo hi low high eqn using forms
  have cov : A = ⋃ i : pieces, valuativeInterval (lo i) (hi i) := by
    rw [hnf.2.1]
    ext z
    simp only [mem_iUnion,exists_prop]
    exact ⟨fun ⟨C,hC,hz⟩ => ⟨⟨C,hC⟩,eqn ⟨C,hC⟩ ▸ hz⟩,
      fun ⟨i,hi⟩ => ⟨i.val,i.property,(eqn i).symm ▸ hi⟩⟩
  have defPiece := fixed_base_holly_components O F.le hF.le hd hnf
  apply cut_disc_meets_base O hO d A base lo hi cov (fun i e h => h.elim (low i e) (high i e)) _ meets misses
  intro i e he sub
  have endDefs := (definable₁_valuativeInterval_iff_ends O hO hF
    (eqn i ▸ (hnf.1 i.val i.property).1) (low i) (high i)).mp (eqn i ▸ defPiece _ i.property)
  have ed := he.elim (endDefs.1 e) (endDefs.2 e)
  have transfer (c : K) (r : O.ValueGroup) (dcl : P.Definable₁ (convexLanguage L) (closedDisc O c r))
      (inside : closedDisc O c r ⊆ d.points O) : (base ∩ d.points O).Nonempty :=
    (closed c r dcl).mono (inter_subset_inter_right _ inside)
  rcases he.elim (low i e) (high i e) with ⟨c,hs⟩ | ⟨c,r,hr,hop | hcl⟩
  · have sing : closedDisc O c 0 = {c} := (closedDiscCode_points O c 0).symm.trans (closedDiscCode_zero_points O c)
    have eq := hs.trans sing.symm
    exact transfer c 0 (eq ▸ ed) (eq ▸ sub.subset)
  · have dcl := definable_closed_parent O hF.toInterpretsFieldTerms hr (hop ▸ ed)
    exact transfer c r dcl (closed_parent_subset_of_proper_open O d hr (hop ▸ sub))
  · exact transfer c r (hcl ▸ ed) (hcl ▸ sub.subset)

end GeneralizedEuler.Section3
