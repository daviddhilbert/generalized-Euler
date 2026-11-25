module

public import Section2.ConvexLanguage
public import Section2.DiscCodes
public import Section2.QuotientInterpretation
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

/-- The multiplicative valuation comparison, including the zero radius. -/
def valuationLEFormula {α : Type a} (F : FieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  (x.equal (zeroTerm F)) ⊔ ((y.equal (zeroTerm F)).not ⊓
    valuationRingFormula (mulTerm F x (invTerm F y)))

set_option linter.style.haveILetI false in
theorem realize_valuationLEFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (x y : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (valuationLEFormula F x y).Realize v ↔ O.valuation (x.realize v) ≤ O.valuation (y.realize v) := by
  letI := convexStructure O L
  simp only [valuationLEFormula, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_equal, realize_valuationRingFormula, realize_zeroTerm O hF, invTerm,
    mulTerm, Term.realize_subst, hF.inv, hF.mul, Fin.cases_zero, finCases_one]
  by_cases hy : y.realize v = 0
  · rw [hy, map_zero, nonpos_iff_eq_zero, map_eq_zero]
    simp
  · rw [← div_eq_mul_inv, ← O.valuation_le_one_iff, map_div₀,
      div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero O.valuation).mpr hy))]
    simp only [hy, not_false_eq_true, true_and]
    exact or_iff_right_of_imp (fun hx => by simp [hx])

/-- Membership in the open or closed disc with a represented radius. -/
def discMemberFormula {α : Type a} (F : FieldTerms (convexLanguage L)) (closed : Bool)
    (x c r : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  if closed then valuationLEFormula F (subTerm F x c) r
  else (valuationLEFormula F r (subTerm F x c)).not

set_option linter.style.haveILetI false in
theorem realize_discMemberFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (closed : Bool) (x c r : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (discMemberFormula F closed x c r).Realize v ↔
      x.realize v ∈ (if closed then closedDisc else openDisc) O (c.realize v) (O.valuation (r.realize v)) := by
  letI := convexStructure O L
  cases closed <;>
    simp [discMemberFormula, realize_valuationLEFormula O hF, subTerm, Term.realize_subst,
      hF.sub, finCases_one, openDisc, closedDisc, not_le]

/-- Equality of disc codes is the first-order equivalence of the
membership formulas on all field points. -/
noncomputable def discEqualFormula {α : Type a} (F : FieldTerms (convexLanguage L))
    (closed₁ closed₂ : Bool) (c r d s : (convexLanguage L).Term α) :
    (convexLanguage L).Formula α :=
  let t : (convexLanguage L).Term (α ⊕ Unit) := .var (.inr ())
  let lift := Term.relabel (L := convexLanguage L) (Sum.inl : α → α ⊕ Unit)
  Formula.iAlls Unit ((discMemberFormula F closed₁ t (lift c) (lift r)).iff
    (discMemberFormula F closed₂ t (lift d) (lift s)))

set_option linter.style.haveILetI false in
theorem realize_discEqualFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (closed₁ closed₂ : Bool) (c r d s : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (discEqualFormula F closed₁ closed₂ c r d s).Realize v ↔
      (if closed₁ then closedDisc else openDisc) O (c.realize v) (O.valuation (r.realize v)) =
      (if closed₂ then closedDisc else openDisc) O (d.realize v) (O.valuation (s.realize v)) := by
  letI := convexStructure O L
  simp only [discEqualFormula, Formula.realize_iAlls, Formula.realize_iff,
    realize_discMemberFormula O hF, Term.realize_relabel, Term.realize_var, Sum.elim_inr,
    Sum.elim_comp_inl]
  rw [Set.ext_iff]
  exact ⟨fun h x => h (fun _ => x), fun h f => h (f ())⟩

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

/-- Whether a field term represents a point of the embedded residue field. -/
def residueFormula {α : Type a} (F : FieldTerms (convexLanguage L))
    (x : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  (x.equal (zeroTerm F)) ⊔ residueNonzeroFormula F x

set_option linter.style.haveILetI false in
theorem realize_residueFormula {α : Type a} {F : FieldTerms (convexLanguage L)}
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
      exact mem_ring_of_rv_mem_residue O (hargs i)
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

section PowerGraph

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The total field function representing a named power on all RV
classes, with the manuscript's extension by zero. -/
def totalFieldPower (g : PositiveField K →* PositiveField K) (x : K) : K :=
  if hx : 0 < x then g ⟨x, hx⟩ else 0

theorem totalFieldPower_positive (g : PositiveField K →* PositiveField K) (x : PositiveField K) :
    totalFieldPower g (x : K) = (g x : K) := by
  rw [totalFieldPower, dite_eq_left x.property]

theorem totalFieldPower_of_not_pos (g : PositiveField K →* PositiveField K) {x : K}
    (hx : ¬ 0 < x) : totalFieldPower g x = 0 := by
  rw [totalFieldPower, dite_eq_right hx]

/-- Apply a field power to an input representative and compare leading
terms with its output representative. -/
noncomputable def rvPowerGraphFormula (F : FieldTerms (convexLanguage L))
    (graph : (convexLanguage L).Formula (Fin 2)) :
    (convexLanguage L).Formula (Option (Fin 1)) :=
  Formula.iExs Unit
    (graph.relabel (Fin.cases (.inl (some 0)) (fun _ => .inr ())) ⊓
      rvEqualFormula F (.var (.inl none)) (.var (.inr ())))

set_option linter.style.haveILetI false in
theorem realize_rvPowerGraphFormula (hO : IsOrderConvex O)
    {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (graph : (convexLanguage L).Formula (Fin 2))
    (g : PositiveField K →* PositiveField K) (P : RV0 O → RV0 O)
    (hgraph : letI := convexStructure O L
      ∀ v : Fin 2 → K, graph.Realize v ↔ totalFieldPower g (v 0) = v 1)
    (hP : AgreesWithFieldPower O g P) (hP₀ : ∀ t, ¬IsPositiveRV O t → P t = 0)
    (v : Option (Fin 1) → K) :
    letI := convexStructure O L
    (rvPowerGraphFormula F graph).Realize v ↔ rv O (v none) = P (rv O (v (some 0))) := by
  letI := convexStructure O L
  simp only [rvPowerGraphFormula, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_relabel, hgraph, realize_rvEqualFormula O hF, Term.realize_var,
    Function.comp_apply, Fin.cases_zero, finCases_one, Sum.elim_inl, Sum.elim_inr]
  have htotal : rv O (totalFieldPower g (v (some 0))) = P (rv O (v (some 0))) := by
    unfold totalFieldPower
    split
    next h => exact (hP ⟨v (some 0), h⟩).symm
    next h => rw [map_zero, hP₀ _ (fun hp => h ((isPositiveRV_rv_iff O hO).mp hp))]
  constructor
  · rintro ⟨w, hw, hrv⟩
    exact hrv.trans ((congrArg (rv O) hw).symm.trans htotal)
  · intro h
    exact ⟨fun _ => totalFieldPower g (v (some 0)), rfl, h.trans htotal.symm⟩

end PowerGraph

/-- The remaining field primitives used to interpret the signed order and
the distinguished RV unit. -/
structure OrderedFieldTerms (J : Language.{u, v}) extends FieldTerms J where
  one : J.Term Empty
  le : J.Relations 2

structure InterpretsOrderedFieldTerms {J : Language.{u, v}} {A : Type*}
    [Field A] [LinearOrder A] [J.Structure A] (F : OrderedFieldTerms J) : Prop
    extends InterpretsFieldTerms (K := A) F.toFieldTerms where
  one : F.one.realize (Empty.elim : Empty → A) = 1
  le : ∀ x : Fin 2 → A, Structure.RelMap F.le x ↔ x 0 ≤ x 1

private def argumentTerms (s : TCsort) {n : ℕ} :
    Fin n → (convexLanguage L).Term (Option (Fin (List.replicate n s).length)) :=
  homogeneousArgs (X := fun _ => (convexLanguage L).Term _) (s := s) (fun i => .var (some i))

private def relationTerms (s : TCsort) {n : ℕ} :
    Fin n → (convexLanguage L).Term (Fin (List.replicate n s).length) :=
  homogeneousArgs (X := fun _ => (convexLanguage L).Term _) (s := s) (fun i => .var i)

private def fieldOrderFormula {α : Type a} (F : OrderedFieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term α) : (convexLanguage L).Formula α :=
  Relations.formula F.le (Fin.cases x (fun _ => y))

set_option linter.style.haveILetI false in
private theorem realize_fieldOrderFormula [LinearOrder K] {α : Type a}
    {F : OrderedFieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
    (x y : (convexLanguage L).Term α) (v : α → K) :
    letI := convexStructure O L
    (fieldOrderFormula F x y).Realize v ↔ x.realize v ≤ y.realize v := by
  letI := convexStructure O L
  simp only [fieldOrderFormula, Formula.realize_rel, hF.le, Fin.cases_zero, finCases_one]

/-- The valuation-ring test when some variables are bound. -/
def valuationRingBoundedFormula {α : Type a} {n : ℕ}
    (x : (convexLanguage L).Term (α ⊕ Fin n)) : (convexLanguage L).BoundedFormula α n :=
  .rel (.inr RingPredicate.mem) (fun _ => x)

set_option linter.style.haveILetI false in
theorem realize_valuationRingBoundedFormula {α : Type a} {n : ℕ}
    (x : (convexLanguage L).Term (α ⊕ Fin n)) (v : α → K) (xs : Fin n → K) :
    letI := convexStructure O L
    (valuationRingBoundedFormula x).Realize v xs ↔ x.realize (Sum.elim v xs) ∈ O := by
  letI := convexStructure O L
  exact convexStructure_mem O (fun _ => x.realize (Sum.elim v xs))

/-- Equality in the residue field on terms whose values are integral. -/
def residueEqBoundedFormula {α : Type a} {n : ℕ} (F : FieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term (α ⊕ Fin n)) : (convexLanguage L).BoundedFormula α n :=
  ((subTerm F x y).bdEqual (zeroTerm F)) ⊔
    (valuationRingBoundedFormula (invTerm F (subTerm F x y))).not

set_option linter.style.haveILetI false in
theorem realize_residueEqBoundedFormula {α : Type a} {n : ℕ}
    {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (x y : (convexLanguage L).Term (α ⊕ Fin n)) (v : α → K) (xs : Fin n → K)
    (hx : letI := convexStructure O L; x.realize (Sum.elim v xs) ∈ O)
    (hy : letI := convexStructure O L; y.realize (Sum.elim v xs) ∈ O) :
    letI := convexStructure O L
    (residueEqBoundedFormula F x y).Realize v xs ↔
      IsLocalRing.residue O ⟨x.realize (Sum.elim v xs), hx⟩ =
        IsLocalRing.residue O ⟨y.realize (Sum.elim v xs), hy⟩ := by
  letI := convexStructure O L
  rw [residue_eq_iff_valuation_sub_lt_one]
  simp only [residueEqBoundedFormula, BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_not, realize_valuationRingBoundedFormula O, realize_zeroTerm O hF,
    invTerm, subTerm, Term.realize_subst, hF.inv, hF.sub, Fin.cases_zero, finCases_one]
  exact (O.mem_nonunits_iff_or.symm.trans O.mem_nonunits_iff)

/-- The inherited residue order is the quotient order on integral terms. -/
def residueLEBoundedFormula {α : Type a} {n : ℕ} (F : OrderedFieldTerms (convexLanguage L))
    (x y : (convexLanguage L).Term (α ⊕ Fin n)) : (convexLanguage L).BoundedFormula α n :=
  F.le.boundedFormula (Fin.cases x (fun _ => y)) ⊔ residueEqBoundedFormula F.toFieldTerms x y

set_option linter.style.haveILetI false in
theorem realize_residueLEBoundedFormula [LinearOrder K] [IsStrictOrderedRing K]
    (hO : IsOrderConvex O) {α : Type a} {n : ℕ} {F : OrderedFieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
    (x y : (convexLanguage L).Term (α ⊕ Fin n)) (v : α → K) (xs : Fin n → K)
    (hx : letI := convexStructure O L; x.realize (Sum.elim v xs) ∈ O)
    (hy : letI := convexStructure O L; y.realize (Sum.elim v xs) ∈ O) :
    letI := convexStructure O L
    letI := residueLinearOrder O hO
    (residueLEBoundedFormula F x y).Realize v xs ↔
      IsLocalRing.residue O ⟨x.realize (Sum.elim v xs), hx⟩ ≤
        IsLocalRing.residue O ⟨y.realize (Sum.elim v xs), hy⟩ := by
  letI := convexStructure O L
  letI := residueLinearOrder O hO
  simp only [residueLEBoundedFormula, BoundedFormula.realize_sup, BoundedFormula.realize_rel,
    hF.le, Fin.cases_zero, finCases_one,
    realize_residueEqBoundedFormula O hF.toInterpretsFieldTerms x y v xs hx hy]
  exact (residue_le_residue_iff O hO
    (x := ⟨_, hx⟩) (y := ⟨_, hy⟩)).symm

universe w
variable {E : Type w}

/-- Interpret the full signature on field representatives. The field graphs
for the named powers and the represented graphs for residue primitives are
the symbol-specific inputs. All other formulas are uniform in those graphs. -/
noncomputable def canonicalQuotientInterpretation
    (F : OrderedFieldTerms (convexLanguage L))
    (residue : ∀ {n} (_f : L.Functions n),
      (convexLanguage L).Formula (Option (Fin (List.replicate n TCsort.rv).length)))
    (power : E → (convexLanguage L).Formula (Fin 2)) :
    QuotientInterpretation (convexLanguage L) L E where
  equal
    | .vf => (Term.var (0 : Fin 2)).equal (.var 1)
    | .rv => rvEqualFormula F.toFieldTerms (.var 0) (.var 1)
  function
    | .vf f => (Term.var none).equal
        (.func ((LHom.sumInl : L →ᴸ convexLanguage L).onFunction f) (argumentTerms .vf))
    | .rvZero => (Term.var none).equal (zeroTerm F.toFieldTerms)
    | .rvOne => rvEqualFormula F.toFieldTerms (.var none) (F.one.relabel Empty.elim)
    | .rvMul => rvEqualFormula F.toFieldTerms (.var none)
        (mulTerm F.toFieldTerms (.var (some 0)) (.var (some 1)))
    | .rvInv => rvEqualFormula F.toFieldTerms (.var none)
        (invTerm F.toFieldTerms (.var (some 0)))
    | .residue f => residue f
    | .power e => rvPowerGraphFormula F.toFieldTerms (power e)
    | .rv => rvEqualFormula F.toFieldTerms (.var none) (.var (some 0))
  relation
    | .vf r => Relations.formula ((LHom.sumInl : L →ᴸ convexLanguage L).onRelation r)
        (relationTerms .vf)
    | .residueNonzero => residueNonzeroFormula F.toFieldTerms (.var 0)
    | .rvLE => fieldOrderFormula F (.var 0) (.var 1) ⊔
        rvEqualFormula F.toFieldTerms (.var 0) (.var 1)

section CanonicalInterpretation

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure (Residue O)]

set_option linter.style.haveILetI false in
/-- On canonical models the formulas give the quotient structure used in
Theorem 2.14. -/
noncomputable def realizesCanonicalQuotientInterpretation (hO : IsOrderConvex O)
    (F : OrderedFieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
    (residue : ∀ {n} (_f : L.Functions n),
      (convexLanguage L).Formula (Option (Fin (List.replicate n TCsort.rv).length)))
    (power : E → (convexLanguage L).Formula (Fin 2))
    (g : E → PositiveField K →* PositiveField K) (P : E → RV0 O → RV0 O)
    (hpower : letI := convexStructure O L
      ∀ e (v : Fin 2 → K), (power e).Realize v ↔ totalFieldPower (g e) (v 0) = v 1)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hP₀ : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hresidue : letI := convexStructure O L
      ∀ {n} (f : L.Functions n) (v : Option (Fin (List.replicate n TCsort.rv).length) → K),
        (residue f).Realize v ↔ rv O (v none) = extendResidueOperation O (Structure.funMap f)
          (rv O ∘ homogeneousArgs (X := fun _ => K) (s := .rv) (fun i => v (some i)))) :
    letI := convexStructure O L
    RealizesQuotientInterpretation (canonicalQuotientInterpretation F residue power) (A := K)
      (canonicalStructure O hO P) := by
  letI := convexStructure O L
  letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K :=
    convexStructure_expansion O
  let q : ∀ s, K → CanonicalSort O s
    | .vf => id
    | .rv => rv O
  refine { rep := q
           surjective := fun s => match s with
             | .vf => Function.surjective_id
             | .rv => rv_surjective O
           equal := ?_, function := ?_, relation := ?_ }
  · intro s v
    cases s
    · exact Formula.realize_equal
    · exact realize_rvEqualFormula O hF.toInterpretsFieldTerms _ _ v
  · intro ss s f v
    cases f with
    | vf f =>
      change ((Term.var none).equal (Term.func ((LHom.sumInl : L →ᴸ convexLanguage L).onFunction f)
        (argumentTerms .vf))).Realize v ↔ _
      rw [Formula.realize_equal, Term.realize_var, Term.realize_func,
        LHom.map_onFunction (LHom.sumInl : L →ᴸ convexLanguage L)]
      have hargs : (fun i => (argumentTerms .vf i).realize v) =
          homogeneousArgs (X := fun _ => K) (s := .vf) (fun i => v (some i)) :=
        (homogeneousArgs_map (X := fun _ => (convexLanguage L).Term _)
          (Y := fun _ => K) (s := .vf) (fun _ x => x.realize v) (fun i => .var (some i))).symm
      change (v none = Structure.funMap f (fun i => (argumentTerms .vf i).realize v)) ↔
        v none = Structure.funMap f
          (homogeneousArgs (fun i => q _ (v (some i))))
      rw [homogeneousArgs_map q, hargs]
      rfl
    | rvZero =>
      change ((Term.var none).equal (zeroTerm F.toFieldTerms)).Realize v ↔ rv O (v none) = 0
      rw [Formula.realize_equal, Term.realize_var, realize_zeroTerm O hF.toInterpretsFieldTerms,
        rv_eq_zero_iff]
    | rvOne =>
      change (rvEqualFormula F.toFieldTerms (.var none) (F.one.relabel Empty.elim)).Realize v ↔
        rv O (v none) = 1
      rw [realize_rvEqualFormula O hF.toInterpretsFieldTerms, Term.realize_var,
        Term.realize_relabel, Subsingleton.elim (v ∘ Empty.elim) (Empty.elim : Empty → K),
        hF.one, map_one]
    | rvMul =>
      simp only [canonicalQuotientInterpretation, canonicalStructure,
        realize_rvEqualFormula O hF.toInterpretsFieldTerms, mulTerm, Term.realize_subst,
        hF.mul, Fin.cases_zero, finCases_one, Term.realize_var, map_mul]
      rfl
    | rvInv =>
      simp only [canonicalQuotientInterpretation, canonicalStructure,
        realize_rvEqualFormula O hF.toInterpretsFieldTerms, invTerm, Term.realize_subst,
        hF.inv, Term.realize_var, map_inv₀]
      rfl
    | residue f =>
      change (residue f).Realize v ↔ rv O (v none) =
        extendResidueOperation O (Structure.funMap f) (homogeneousArgs (fun i => q _ (v (some i))))
      rw [homogeneousArgs_map q]
      exact hresidue f v
    | power e =>
      exact realize_rvPowerGraphFormula O hO hF.toInterpretsFieldTerms
        (power e) (g e) (P e) (hpower e) (hP e) (hP₀ e) v
    | rv => exact realize_rvEqualFormula O hF.toInterpretsFieldTerms _ _ v
  · intro ss r v
    cases r with
    | vf r =>
      change (Relations.formula ((LHom.sumInl : L →ᴸ convexLanguage L).onRelation r)
        (relationTerms .vf)).Realize v ↔ _
      rw [Formula.realize_rel, LHom.map_onRelation (LHom.sumInl : L →ᴸ convexLanguage L)]
      have hargs : (fun i => (relationTerms .vf i).realize v) =
          homogeneousArgs (X := fun _ => K) (s := .vf) v :=
        (homogeneousArgs_map (X := fun _ => (convexLanguage L).Term _)
          (Y := fun _ => K) (s := .vf) (fun _ x => x.realize v) Term.var).symm
      change Structure.RelMap r (fun i => (relationTerms .vf i).realize v) ↔
        Structure.RelMap r (homogeneousArgs (fun i => q _ (v i)))
      rw [homogeneousArgs_map q, hargs]
      rfl
    | residueNonzero => exact realize_residueNonzeroFormula O hF.toInterpretsFieldTerms _ v
    | rvLE =>
      change (fieldOrderFormula F (.var 0) (.var 1) ⊔
        rvEqualFormula F.toFieldTerms (.var 0) (.var 1)).Realize v ↔ _
      rw [Formula.realize_sup, realize_fieldOrderFormula O hF,
        realize_rvEqualFormula O hF.toInterpretsFieldTerms]
      exact (rv_le_rv_iff O hO).symm

end CanonicalInterpretation

end GeneralizedEuler.Section2
