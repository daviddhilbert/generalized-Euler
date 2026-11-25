module

public import Section3.ResidueChartGraph
public import Section2.RecoveredValuedField
public import Section2.ResidueClassification
import all Section3.ResidueChartGraph
import all Section3.BoundaryBranches
import all Section2.ResidueOrder
import all Section2.ResidueClassification
import all Section2.SortedSyntax
import all Section2.PowerBounded

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set
universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
    {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O) (powers : E → RV0 O → RV0 O)

private theorem definable_rv_image_of_field_set {n : ℕ} (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1) (S : Set (Fin n → K)) :
    letI := convexStructure O L
    (univ : Set K).Definable (convexLanguage L) S →
    SortedDefinableOver (canonicalStructure (L := L) O hO powers) (fun _ => univ)
      {v : ∀ s, RVVariables (Fin n) s → CanonicalSort O s | v .rv ∈ (fun x => (rv O) ∘ x) '' S} := by
  let := convexStructure O L
  intro hS
  obtain ⟨φ,hφ⟩ := definable_iff_exists_formula_sum.mp hS
  let M := canonicalStructure (L := L) O hO powers
  let V (s) := (univ : Set (CanonicalSort O s)) ⊕ RVVariables (Fin n) s
  let W := AddSortedBlock V .vf n
  let x (j : Fin n) : SortedTerm L E W .vf := .var (.inr ⟨j,⟨rfl⟩⟩)
  let par (a : (univ : Set K)) : SortedTerm L E W .vf := .var (.inl (.inl a))
  let pred := liftValuedFormula minusOne φ (Sum.elim (Sum.elim par x) Fin.elim0)
  let matchRV := SortedFormula.allOf (List.ofFn (fun i : Fin n => SortedFormula.equal (rvOf (x i))
    (.var (.inl (.inr i)))))
  refine ⟨(pred.conjunction matchRV).exBlock .vf n,fun v => ?_⟩
  let p (s : TCsort) : V s → CanonicalSort O s := Sum.elim (fun a => a.val) (v s)
  have test (a : Fin n → K) : pred.realize M (appendSortedBlock p a) ↔ a ∈ S := by
    dsimp only [pred]
    rw [realize_liftValuedFormula,recoveredValuedStructure_canonical_eq O hO powers minusOne hm]
    have he (e : Fin 0 → K) : BoundedFormula.Realize φ (Sum.elim Subtype.val a) e ↔ a ∈ S := by
      rw [Subsingleton.elim e default]; exact (Set.ext_iff.mp hφ a).symm
    have args : (fun i => ((Sum.elim par x) i).realize M (appendSortedBlock p a)) = Sum.elim Subtype.val a := by
      funext i; cases i <;> rfl
    simp only [Sum.elim_inl,args]
    apply he
  have eqn (a : Fin n → K) : matchRV.realize M (appendSortedBlock p a) ↔ (rv O) ∘ a = v .rv := by
    simp only [matchRV,SortedFormula.realize_allOf,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
      SortedFormula.realize,rvOf_realize,x,SortedTerm.realize,appendSortedBlock,p,Sum.elim_inr]
    change (∀ i, (canonicalStructure (L := L) O hO powers).rvMap (a i) = _) ↔ _
    simp only [canonicalStructure_rvMap]
    exact funext_iff.symm
  change (∃ a ∈ S, (rv O) ∘ a = v .rv) ↔ _
  rw [SortedFormula.realize_exBlock]
  apply exists_congr; intro a
  exact ((test a).and (eqn a)).symm.trans (SortedFormula.realize_conjunction M _ _ _).symm

/-- From a definable graph on integral representatives to its ordinary
residue-field graph using exactly the induced-residue hypothesis from
Section 2. Zero is represented by zero in the embedded RV coordinates. -/
theorem definable_residue_pair_of_lift {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (induced : HasInducedResidueDefinability (L := L) O (canonicalStructure O hO powers)) (D : Set (Residue O × Residue O)) :
    letI := convexStructure O L
    (univ : Set K).Definable (convexLanguage L) (residuePairLift O D) →
      (univ : Set (Residue O)).Definable₂ L D := by
  let := convexStructure O L
  intro hD
  let S := {w : Fin 2 → K | w ∈ residuePairLift O D ∧ ∀ i, rv O (w i) ∈ range (residueRV O)}
  have dCoord i : (univ : Set K).Definable (convexLanguage L) {w : Fin 2 → K | rv O (w i) ∈ range (residueRV O)} := by
    refine ⟨((convexLanguage L).lhomWithConstants (univ : Set K)).onFormula (residueFormula F (.var i)),?_⟩
    ext w
    exact ((LHom.realize_onFormula _ _).trans (realize_residueFormula O hF (.var i) w)).symm
  have dS : (univ : Set K).Definable (convexLanguage L) S := by
    convert hD.inter (definable_iInter_of_finite dCoord) using 1
    ext w; simp only [S,mem_inter_iff,mem_ofPred_eq,mem_iInter]
  let R := {t : Fin 2 → Residue O | (t 0,t 1) ∈ D}
  have im : (fun w : Fin 2 → K => (rv O) ∘ w) '' S = embeddedResidueSet O R := by
    rw [embeddedResidueSet_eq_image]
    ext t
    constructor
    · rintro ⟨w,⟨⟨a,b,ha,hb,hr⟩,unit⟩,rfl⟩
      refine ⟨![IsLocalRing.residue O a,IsLocalRing.residue O b],hr,?_⟩
      have one (z : O) (hz : rv O (z : K) ∈ range (residueRV O)) :
          residueRV O (IsLocalRing.residue O z) = rv O (z : K) := by
        have h := residueRV_rvResidue_of_mem_range O hz
        rwa [rvResidue_rv,totalResidue_of_mem O z.property] at h
      funext i; fin_cases i
      · change residueRV O (IsLocalRing.residue O a) = rv O (w 0)
        rw [←ha]; exact one a (ha.symm ▸ unit 0)
      · change residueRV O (IsLocalRing.residue O b) = rv O (w 1)
        rw [←hb]; exact one b (hb.symm ▸ unit 1)
    · rintro ⟨v,hv,rfl⟩
      choose a hr he using fun i => exists_residueRV_representative O (v i)
      exact ⟨fun i => (a i : K),⟨⟨a 0,a 1,rfl,rfl,by rw [hr,hr]; exact hv⟩,fun i => ⟨_,(he i).symm⟩⟩,funext he⟩
  apply (induced R).mpr
  rw [←im]
  exact definable_rv_image_of_field_set O hO powers minusOne hm S dS

/-- The obstruction in Lemma 3.34 from the field graph itself. The
ordinary residue graph is derived from Theorem A, including a possible
reflection of the target ray in the subsequent affine argument. -/
theorem no_definable_closed_disc_to_half [DenselyOrdered O.ValueGroup] {I : Type*}
    {F : FieldTerms (convexLanguage L)} (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (induced : HasInducedResidueDefinability (L := L) O (canonicalStructure O hO powers))
    {c d a b : K} {r s : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (hs : s ≠ 0) (hb : O.valuation b = s) (dp : 0 < d) (bp : 0 < b) (upper : Bool) {f g : K → K}
    (hmap : DiscToDiscOn O (closedDisc O c r) (annulusSide upper (openDisc O a s) (closedDisc O a s)) f g)
    (mon : StrictMonoOn f (closedDisc O c r) ∨ StrictAntiOn f (closedDisc O c r))
    (auts : I → MarkedDiscAutomorphism (L := L) O c r a s f)
    (trans : ∀ x y : closedDisc O c r, ∃ i, (auts i).fieldMap x.val = y.val)
    (graph : letI := convexStructure O L
      (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph (closedDisc O c r) f)) :
    letI := residueLinearOrder O hO
    letI := residue_isOrderedRing O hO
    IsOMinimal (K := Residue O) L → IsPowerBounded (K := Residue O) L →
    ∀ {T : OrderedFieldTerms L}, InterpretsOrderedFieldTerms (A := Residue O) T → False :=
  no_closed_disc_to_half O hO hr hd hs hb dp bp upper hmap mon auts trans
    (fun h maps link => definable_residue_pair_of_lift O hO powers hF minusOne hm induced _
      (definable_child_chart_lift O hF hr hd hs hb f h maps link graph))

end GeneralizedEuler.Section3
