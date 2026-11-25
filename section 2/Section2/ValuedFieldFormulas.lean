module

public import Section2.ConvexLanguage
public import Section2.SortedStructure

/-! Formulas for leading-term equality and the residue predicate in
the one-sorted valued-field language. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v a

variable {L : Language.{u, v}}

/-- Terms naming the indicated ordered-field operations in the chosen
functional presentation of T. -/
structure FieldTerms (L : Language.{u, v}) where
  zero : L.Term Empty
  sub : L.Term (Fin 2)
  mul : L.Term (Fin 2)
  inv : L.Term (Fin 1)

structure InterpretsFieldTerms {K : Type*} [Field K] [L.Structure K]
    (F : FieldTerms L) : Prop where
  zero : F.zero.realize (Empty.elim : Empty → K) = 0
  sub : ∀ x : Fin 2 → K, F.sub.realize x = x 0 - x 1
  mul : ∀ x : Fin 2 → K, F.mul.realize x = x 0 * x 1
  inv : ∀ x : Fin 1 → K, F.inv.realize x = (x 0)⁻¹

variable {K : Type*} [Field K] [L.Structure K] (O : ValuationSubring K)

private def zeroTerm {α : Type a} (F : FieldTerms (convexLanguage L)) :
    (convexLanguage L).Term α :=
  F.zero.relabel Empty.elim

private def subTerm {α : Type a} (F : FieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term α) : (convexLanguage L).Term α :=
  F.sub.subst (Fin.cases x (fun _ => y))

private def mulTerm {α : Type a} (F : FieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term α) : (convexLanguage L).Term α :=
  F.mul.subst (Fin.cases x (fun _ => y))

private def invTerm {α : Type a} (F : FieldTerms (convexLanguage L))
    (x : (convexLanguage L).Term α) : (convexLanguage L).Term α :=
  F.inv.subst (fun _ => x)

private theorem finCases_one {A : Type*} (a b : A) :
    (Fin.cases a (fun _ => b) : Fin 2 → A) 1 = b := by rfl

set_option linter.style.haveILetI false in
private theorem realize_zeroTerm {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) (v : α → K) :
    letI := convexStructure O L
    (zeroTerm F).realize v = 0 := by
  letI := convexStructure O L
  rw [zeroTerm, Term.realize_relabel]
  exact Subsingleton.elim (v ∘ Empty.elim) (Empty.elim : Empty → K) ▸ hF.zero

/-- The valuation-ring predicate on a valued-field term. -/
def valuationRingFormula {α : Type a} (x : (convexLanguage L).Term α) :
    (convexLanguage L).Formula α :=
  Relations.formula (.inr RingPredicate.mem) (fun _ => x)

set_option linter.style.haveILetI false in
theorem realize_valuationRingFormula {α : Type a} (x : (convexLanguage L).Term α)
    (v : α → K) :
    letI := convexStructure O L
    (valuationRingFormula x).Realize v ↔ x.realize v ∈ O := by
  letI := convexStructure O L
  rw [valuationRingFormula]
  exact (Formula.realize_rel (L := convexLanguage L) (R := .inr RingPredicate.mem)
    (ts := fun _ => x)).trans (convexStructure_mem O (fun _ => x.realize v))

/-- A valued-field formula for equality of two represented leading terms. -/
def rvEqualFormula {α : Type a} (F : FieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  (x.equal y) ⊔ ((y.equal (zeroTerm F)).not ⊓
    (valuationRingFormula (invTerm F (mulTerm F (subTerm F x y) (invTerm F y)))).not)

theorem rvEqualFormula_isQF {α : Type a} (F : FieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term α) : (rvEqualFormula F x y).IsQF := by
  have equal_isQF (u v : (convexLanguage L).Term α) : (u.equal v).IsQF :=
    (BoundedFormula.IsAtomic.equal _ _).isQF
  have ring_isQF (u : (convexLanguage L).Term α) : (valuationRingFormula u).IsQF :=
    (BoundedFormula.IsAtomic.rel _ _).isQF
  exact (equal_isQF x y).sup
    ((equal_isQF y (zeroTerm F)).not.inf (ring_isQF _).not)

set_option linter.style.haveILetI false in
theorem realize_rvEqualFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (x y : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (rvEqualFormula F x y).Realize v ↔ rv O (x.realize v) = rv O (y.realize v) := by
  letI := convexStructure O L
  simp only [rvEqualFormula, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_equal, realize_valuationRingFormula, realize_zeroTerm O hF, invTerm,
    mulTerm, subTerm, Term.realize_subst, hF.inv, hF.mul, hF.sub, Fin.cases_zero, finCases_one]
  by_cases hy : y.realize v = 0
  · simp [hy]
  · rw [rv_eq_rv_iff_ring O hy, div_eq_mul_inv]
    simp [hy]

set_option linter.style.haveILetI false in
/-- A common valued-field substructure preserves equality with any
named leading-term representative. This is the syntactic step in the
second stage of Lemma 2.20. -/
theorem rv_eq_iff_of_pair_embeddings
    {A F : Type*} [(convexLanguage L).Structure A] [Field F] [L.Structure F]
    (P : ValuationSubring F) (t : FieldTerms (convexLanguage L))
    (hK : letI := convexStructure O L; InterpretsFieldTerms (K := K) t)
    (hF : letI := convexStructure P L; InterpretsFieldTerms (K := F) t) :
    letI := convexStructure O L
    letI := convexStructure P L
    ∀ (i : A ↪[convexLanguage L] K) (j : A ↪[convexLanguage L] F) (v : Fin 2 → A),
      rv O (i (v 0)) = rv O (i (v 1)) ↔ rv P (j (v 0)) = rv P (j (v 1)) := by
  letI := convexStructure O L
  letI := convexStructure P L
  intro i j v
  let ψ := rvEqualFormula t (.var (0 : Fin 2)) (.var (1 : Fin 2))
  have hq : ψ.IsQF := rvEqualFormula_isQF _ _ _
  have hi := hq.realize_embedding i (v := v) (xs := default)
  have hj := hq.realize_embedding j (v := v) (xs := default)
  rw [Subsingleton.elim (i ∘ (default : Fin 0 → A)) (default : Fin 0 → K)] at hi
  rw [Subsingleton.elim (j ∘ (default : Fin 0 → A)) (default : Fin 0 → F)] at hj
  have hFormula : ψ.Realize (i ∘ v) ↔ ψ.Realize (j ∘ v) := hi.trans hj.symm
  exact (realize_rvEqualFormula O hK _ _ (i ∘ v)).symm.trans
    (hFormula.trans (realize_rvEqualFormula P hF _ _ (j ∘ v)))

/-- The unary auxiliary predicate is represented by the field units
of the valuation ring. -/
def residueNonzeroFormula {α : Type a} (F : FieldTerms (convexLanguage L))
    (x : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  (x.equal (zeroTerm F)).not ⊓
    (valuationRingFormula x ⊓ valuationRingFormula (invTerm F x))

set_option linter.style.haveILetI false in
theorem realize_residueNonzeroFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (x : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (residueNonzeroFormula F x).Realize v ↔ unsignedValue O (rv O (x.realize v)) = 1 := by
  letI := convexStructure O L
  simp only [residueNonzeroFormula, Formula.realize_inf, Formula.realize_not,
    Formula.realize_equal, realize_valuationRingFormula, realize_zeroTerm O hF, invTerm,
    Term.realize_subst, hF.inv, unsignedValue_rv, valuation_eq_one_iff_mem_and_inv]

private def residueFormula {α : Type a} (F : FieldTerms (convexLanguage L))
    (x : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  (x.equal (zeroTerm F)) ⊔ residueNonzeroFormula F x

set_option linter.style.haveILetI false in
private theorem realize_residueFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (x : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (residueFormula F x).Realize v ↔ rv O (x.realize v) ∈ Set.range (residueRV O) := by
  letI := convexStructure O L
  rw [range_residueRV]
  simp only [residueFormula, Formula.realize_sup, Formula.realize_equal,
    realize_zeroTerm O hF, realize_residueNonzeroFormula O hF, Set.mem_ofPred_eq, rv_eq_zero_iff]

private def residueEqualFormula {α : Type a} (F : FieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  residueFormula F x ⊓ ((subTerm F x y).equal (zeroTerm F) ⊔
    (valuationRingFormula (invTerm F (subTerm F x y))).not)

set_option linter.style.haveILetI false in
private theorem realize_residueEqualFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (x y : (convexLanguage L).Term α) (v : α → K)
    (hy : letI := convexStructure O L; y.realize v ∈ O) :
    letI := convexStructure O L
    (residueEqualFormula F x y).Realize v ↔
      rv O (x.realize v) = residueRV O (IsLocalRing.residue O ⟨y.realize v, hy⟩) := by
  letI := convexStructure O L
  rw [residueEqualFormula, Formula.realize_inf, realize_residueFormula O hF,
    range_residueRV, rv_eq_residueRV_residue_iff]
  simp only [Formula.realize_sup, Formula.realize_equal, realize_zeroTerm O hF,
    Formula.realize_not, realize_valuationRingFormula, subTerm, invTerm,
    Term.realize_subst, hF.inv, hF.sub, Fin.cases_zero, finCases_one, Set.mem_ofPred_eq,
    rv_eq_zero_iff, unsignedValue_rv, O.mem_nonunits_iff_or]

/-- A term whose reduction gives a residue operation yields a graph
formula for the operation extended by zero on RV. -/
noncomputable def residueFunctionFormula {α : Type a} {n : ℕ}
    (F : FieldTerms (convexLanguage L)) (g : (convexLanguage L).Term (Fin n))
    (x : Fin n → (convexLanguage L).Term α) (y : (convexLanguage L).Term α) :
    (convexLanguage L).Formula α :=
  let inputs := Formula.iInf (fun i => residueFormula F (x i))
  (inputs ⊓ residueEqualFormula F y (g.subst x)) ⊔ (inputs.not ⊓ y.equal (zeroTerm F))

set_option linter.style.haveILetI false in
theorem realize_residueFunctionFormula {α : Type a} {n : ℕ} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (g : (convexLanguage L).Term (Fin n)) (gRes : (Fin n → Residue O) → Residue O)
    (hmatch : letI := convexStructure O L
      ∀ z : Fin n → O, ∃ h : g.realize (fun i => (z i : K)) ∈ O,
        IsLocalRing.residue O ⟨g.realize (fun i => (z i : K)), h⟩ =
          gRes (IsLocalRing.residue O ∘ z))
    (x : Fin n → (convexLanguage L).Term α) (y : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (residueFunctionFormula F g x y).Realize v ↔
      rv O (y.realize v) = extendResidueOperation O gRes (fun i => rv O ((x i).realize v)) := by
  classical
  letI := convexStructure O L
  simp only [residueFunctionFormula, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_not, realize_residueFormula O hF,
    Formula.realize_equal, realize_zeroTerm O hF]
  let args := fun i => rv O ((x i).realize v)
  change ((∀ i, args i ∈ Set.range (residueRV O)) ∧ (residueEqualFormula F y (g.subst x)).Realize v) ∨
    ((¬∀ i, args i ∈ Set.range (residueRV O)) ∧ y.realize v = 0) ↔
      rv O (y.realize v) = extendResidueOperation O gRes args
  by_cases hargs : ∀ i, args i ∈ Set.range (residueRV O)
  · have integral (i : Fin n) : (x i).realize v ∈ O := by
      have hi := hargs i
      change rv O ((x i).realize v) ∈ Set.range (residueRV O) at hi
      rw [range_residueRV, Set.mem_ofPred_eq, rv_eq_zero_iff, unsignedValue_rv] at hi
      rcases hi with hi | hi
      · rw [hi]
        exact O.zero_mem
      · exact (O.valuation_le_one_iff _).mp hi.le
    let z : Fin n → O := fun i => ⟨(x i).realize v, integral i⟩
    obtain ⟨h, he⟩ := hmatch z
    have hout : (g.subst x).realize v ∈ O := by
      rw [Term.realize_subst]
      exact h
    have hres : IsLocalRing.residue O ⟨(g.subst x).realize v, hout⟩ =
        gRes (rvResidue O ∘ args) := by
      have heq : (⟨(g.subst x).realize v, hout⟩ : O) =
          ⟨g.realize (fun i => (z i : K)), h⟩ := Subtype.ext Term.realize_subst
      rw [heq, he]
      congr 1
      funext i
      change IsLocalRing.residue O (z i) = rvResidue O (rv O ((x i).realize v))
      rw [rvResidue_rv, totalResidue_of_mem O (integral i)]
    rw [realize_residueEqualFormula O hF y (g.subst x) v hout,
      extendResidueOperation_of_mem_range O gRes hargs, hres]
    exact ⟨fun h => h.elim And.right (fun ho => (ho.1 hargs).elim),
      fun h => Or.inl ⟨hargs, h⟩⟩
  · obtain ⟨i, hi⟩ := not_forall.mp hargs
    rw [extendResidueOperation_off_residue O gRes ⟨i, hi⟩, rv_eq_zero_iff]
    simp only [hargs, false_and, not_false_eq_true, true_and, false_or]

end GeneralizedEuler.Section2
