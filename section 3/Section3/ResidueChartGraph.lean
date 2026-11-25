module

public import Section3.ClosedRayMap
public import Section2.ValuedFieldFormulas
import all Section2.ValuativeDisc
import all Section2.PowerBounded

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set
variable {K : Type*} [Field K] {L : Language} [L.Structure K] (O : ValuationSubring K)

/-- Pull back both residue coordinates to integral field representatives. -/
def residuePairLift (R : Set (Residue O × Residue O)) : Set (Fin 2 → K) :=
  {w | ∃ x y : O, (x : K) = w 0 ∧ (y : K) = w 1 ∧ (IsLocalRing.residue O x,IsLocalRing.residue O y) ∈ R}

private theorem linear_lift_label (a d : K) {r : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r) (u : O) :
    ∃ mem : a+d*(u : K) ∈ closedDisc O a r, childLabel O a d hr hd ⟨_,mem⟩ = IsLocalRing.residue O u := by
  have dn : d ≠ 0 := (map_ne_zero _).mp (hd.trans_ne hr)
  have inside : a+d*(u : K) ∈ closedDisc O a r := by
    change O.valuation (a+d*(u : K)-a) ≤ r
    rw [add_sub_cancel_left,map_mul,hd]
    exact mul_le_of_le_one_right (zero_le : 0 ≤ r) (O.valuation_le_one u)
  refine ⟨inside,?_⟩
  change IsLocalRing.residue O (normalizedPoint O a d hr hd ⟨_,inside⟩) = _
  congr 1
  apply Subtype.ext
  change (a+d*(u : K)-a)/d = _
  rw [add_sub_cancel_left,mul_comm,mul_div_cancel_right₀ _ dn]

/-- Definability of the graph needed for stable embeddedness in 3.34.
For integral x,y, test the original graph at c+d*x and ask whether its
output lies in the open child of a+b*y. Choosing coordinates allows the
four field chart parameters, but no section of residue is used. -/
theorem definable_child_chart_lift {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {c d a b : K} {r s : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r) (hs : s ≠ 0) (hb : O.valuation b = s)
    (f : K → K) (h : Residue O → Residue O) (maps : MapsTo f (closedDisc O c r) (closedDisc O a s))
    (link : ∀ x : closedDisc O c r, h (childLabel O c d hr hd x) = childLabel O a b hs hb ⟨f x.val,maps x.property⟩) :
    letI := convexStructure O L
    (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph (closedDisc O c r) f) →
    (univ : Set K).Definable (convexLanguage L) (residuePairLift O (fieldGraph univ h)) := by
  let := convexStructure O L
  rintro ⟨φ,hφ⟩
  let J := convexLanguage L
  let P : Set K := univ
  let V := Fin 2 ⊕ Unit
  let inj := J.lhomWithConstants P
  let con (a : K) : (J[[P]]).Term V := (J.con (⟨a,mem_univ _⟩ : P)).term
  let named := fun (i : Fin 2) => (Term.var (.inl i) : (J[[P]]).Term V)
  let y : (J[[P]]).Term V := .var (.inr ())
  let minus (x z : (J[[P]]).Term V) := (inj.onTerm F.sub).subst ![x,z]
  let linear (a d : K) (i : Fin 2) := minus (con a) (minus (con 0) ((inj.onTerm F.mul).subst ![con d,named i]))
  let openT := inj.onFormula (discMemberFormula F false (.var (0 : Fin 3)) (.var 1) (.var 2))
  let target : (J[[P]]).Formula V := openT.subst ![y,linear a b 1,con b]
  let source : (J[[P]]).Formula V := φ.subst ![linear c d 0,y]
  let integral (i : Fin 2) := inj.onFormula (valuationRingFormula (.var i))
  refine ⟨integral 0 ⊓ integral 1 ⊓ Formula.iExs Unit (source ⊓ target),?_⟩
  ext w
  have inO (i) : (integral i).Realize w ↔ w i ∈ O := by
    simp only [integral,LHom.realize_onFormula,realize_valuationRingFormula,Term.realize_var]
  have lin (a d i) (p : V → K) : (linear a d i).realize p = a+d*p (.inl i) := by
    simp [linear,minus,con,named,Term.realize_subst,LHom.realize_onTerm,hF.sub,hF.mul]
  have graph (v : Fin 2 → K) : φ.Realize v ↔ v 0 ∈ closedDisc O c r ∧ v 1 = f (v 0) :=
    (Set.ext_iff.mp hφ v).symm
  have sourceEval (z : Unit → K) : source.Realize (Sum.elim w z) ↔ c+d*w 0 ∈ closedDisc O c r ∧ z () = f (c+d*w 0) := by
    change BoundedFormula.Realize (φ.subst _) _ default ↔ _
    rw [BoundedFormula.realize_subst]
    change φ.Realize _ ↔ _
    rw [graph]; change (linear c d 0).realize (Sum.elim w z) ∈ _ ∧ z () = f ((linear c d 0).realize _) ↔ _; rw [lin]
    rfl
  have targetEval (z : Unit → K) : target.Realize (Sum.elim w z) ↔ z () ∈ openDisc O (a+b*w 1) s := by
    change BoundedFormula.Realize (openT.subst _) _ default ↔ _
    rw [BoundedFormula.realize_subst]
    change (inj.onFormula _).Realize _ ↔ _
    rw [LHom.realize_onFormula,realize_discMemberFormula O hF]
    change z () ∈ openDisc O ((linear a b 1).realize (Sum.elim w z)) (O.valuation b) ↔ _
    rw [lin,hb]; rfl
  simp only [mem_ofPred_eq,Formula.realize_inf,Formula.realize_iExs,inO,sourceEval,targetEval]
  have criterion (u v : O) : IsLocalRing.residue O v = h (IsLocalRing.residue O u) ↔
      f (c+d*(u : K)) ∈ openDisc O (a+b*(v : K)) s := by
    obtain ⟨hu,lu⟩ := linear_lift_label O c d hr hd u
    obtain ⟨hv,lv⟩ := linear_lift_label O a b hs hb v
    rw [←lu,link ⟨_,hu⟩,←lv,eq_comm,childLabel_equal_iff]
  constructor
  · rintro ⟨u,v,hu,hv,_,he⟩
    obtain ⟨src,_⟩ := linear_lift_label O c d hr hd u
    refine ⟨⟨hu ▸ u.property,hv ▸ v.property⟩,fun _ => f (c+d*w 0),⟨hu ▸ src,rfl⟩,?_⟩
    rw [←hu,←hv]; exact (criterion u v).mp he
  · rintro ⟨⟨hu,hv⟩,z,⟨_,eqn⟩,tar⟩
    exact ⟨⟨_,hu⟩,⟨_,hv⟩,rfl,rfl,trivial,(criterion ⟨_,hu⟩ ⟨_,hv⟩).mpr (eqn ▸ tar)⟩

end GeneralizedEuler.Section3
