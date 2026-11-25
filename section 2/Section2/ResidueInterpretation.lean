module

public import Section2.ValuedFieldFormulas

/-! Interpreting the continuous functional presentation of the residue
field by valuation-ring representatives. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w a

/-- The continuous functional sublanguage uses order as its sole relation. -/
inductive FunctionalOrder : ℕ → Type
  | le : FunctionalOrder 2

abbrev OrderedFunctionalLanguage (G : ℕ → Type w) : Language := ⟨G, FunctionalOrder⟩

variable {L : Language.{u, v}} {G : ℕ → Type w}

/-- Replace the continuous primitive functions by their field terms, test
equality and order after reduction, and restrict all quantifiers to the ring. -/
def translateResidueFormula (F : OrderedFieldTerms (convexLanguage L))
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m)) {α : Type a} :
    ∀ {n}, (OrderedFunctionalLanguage G).BoundedFormula α n →
      (convexLanguage L).BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal x y => residueEqBoundedFormula F.toFieldTerms (x.substFunc term) (y.substFunc term)
  | _, .rel FunctionalOrder.le xs =>
    residueLEBoundedFormula F ((xs 0).substFunc term) ((xs 1).substFunc term)
  | _, .imp φ ψ => .imp (translateResidueFormula F term φ) (translateResidueFormula F term ψ)
  | n, .all φ => .all ((valuationRingBoundedFormula (.var (.inr (Fin.last n)))).imp
      (translateResidueFormula F term φ))

variable {K : Type*} [Field K] [L.Structure K] (O : ValuationSubring K)
  [(OrderedFunctionalLanguage G).Structure (Residue O)]

set_option linter.style.haveILetI false in
/-- A family of field terms that realizes the continuous primitives after
reduction on integral inputs. -/
def ResidueTermPresentation (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m)) : Prop :=
  letI := convexStructure O L
  ∀ {m} (f : G m) (z : Fin m → O), ∃ h : (term f).realize (fun i => (z i : K)) ∈ O,
    IsLocalRing.residue O ⟨(term f).realize (fun i => (z i : K)), h⟩ =
      Structure.funMap (L := OrderedFunctionalLanguage G) f (IsLocalRing.residue O ∘ z)

/-- The field term for a symbol of the continuous reduct that is named in
the full functional language. -/
def continuousSymbolTerm (name : ∀ {m}, G m → L.Functions m) {n : ℕ} (f : G n) :
    (convexLanguage L).Term (Fin n) :=
  (LHom.sumInl : L →ᴸ convexLanguage L).onTerm (name f).term

set_option linter.style.haveILetI false in
/-- Ax. 8 gives the required reduction on each continuous primitive. -/
theorem residueTermPresentation_of_matching [TopologicalSpace K] [TopologicalSpace (Residue O)]
    [L.Structure (Residue O)] (H : MatchesContinuousFunctions L O)
    (name : ∀ {m}, G m → L.Functions m)
    (hcontinuous : ∀ {n} (f : G n), Continuous
      (Structure.funMap (name f) : (Fin n → K) → K))
    (hname : ∀ {n} (f : G n) (v : Fin n → Residue O), Structure.funMap (name f) v =
      Structure.funMap (L := OrderedFunctionalLanguage G) f v) :
    ResidueTermPresentation O (continuousSymbolTerm name) := by
  letI := convexStructure O L
  letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K := convexStructure_expansion O
  intro n f a
  let graph : L.Formula (Option (Fin n)) := ((name f).term.relabel some).equal (.var none)
  have hgK : DefinesTotalFunction graph (Structure.funMap (name f) : (Fin n → K) → K) := by
    apply DefinesTotalFunction.of_realize
    intro x
    simp only [graph, Formula.realize_equal, Term.realize_var, Term.realize_relabel,
      Term.realize_function_term]
  have hgR : DefinesTotalFunction graph
      (Structure.funMap (L := OrderedFunctionalLanguage G) f : (Fin n → Residue O) → Residue O) := by
    apply DefinesTotalFunction.of_realize
    intro x
    simp only [graph, Formula.realize_equal, Term.realize_var, Term.realize_relabel,
      Term.realize_function_term, hname]
  have h := H.reduces hgK (hcontinuous f) hgR a
  simp only [continuousSymbolTerm, LHom.realize_onTerm, Term.realize_function_term]
  exact h

set_option linter.style.haveILetI false in
theorem realize_residueTerm {α : Type a}
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m))
    (hterm : ResidueTermPresentation O term) (t : (OrderedFunctionalLanguage G).Term α)
    (z : α → O) :
    letI := convexStructure O L
    ∃ h : (t.substFunc term).realize (fun i => (z i : K)) ∈ O,
      IsLocalRing.residue O ⟨(t.substFunc term).realize (fun i => (z i : K)), h⟩ =
        t.realize (IsLocalRing.residue O ∘ z) := by
  letI := convexStructure O L
  induction t with
  | var i => exact ⟨(z i).property, rfl⟩
  | func f ts ih =>
    let args i : O := ⟨_, (ih i).choose⟩
    have hargs : (IsLocalRing.residue O ∘ args) =
        fun i => (ts i).realize (IsLocalRing.residue O ∘ z) :=
      funext fun i => (ih i).choose_spec
    obtain ⟨hm, hf⟩ := hterm f args
    simp only [Term.substFunc, Term.realize_subst]
    refine ⟨hm, ?_⟩
    rw [hf, hargs, Term.realize_func]

private theorem comp_sumElim {A B C D : Type*} (f : C → D) (v : A → C) (x : B → C) :
    (fun i => f (Sum.elim v x i)) = Sum.elim (f ∘ v) (f ∘ x) := by
  funext i
  cases i <;> rfl

private theorem realize_formula_with_empty_tuple {J : Language} {A α : Type*} [J.Structure A]
    (φ : J.Formula α) (v : α → A) (xs : Fin 0 → A) :
    φ.Realize v ↔ BoundedFormula.Realize φ v xs := by
  unfold Formula.Realize
  rw [Subsingleton.elim (default : Fin 0 → A) xs]

set_option linter.style.haveILetI false in
/-- Truth in the continuous residue language reduces to truth in the
valued-field language over any choice of integral representatives. -/
theorem realize_translateResidueFormula [LinearOrder K] [IsStrictOrderedRing K]
    (hO : IsOrderConvex O) (F : OrderedFieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m))
    (hterm : ResidueTermPresentation O term)
    (horder : letI := residueLinearOrder O hO
      ∀ z : Fin 2 → Residue O,
        Structure.RelMap (L := OrderedFunctionalLanguage G) FunctionalOrder.le z ↔ z 0 ≤ z 1)
    {α : Type a} {n : ℕ} (φ : (OrderedFunctionalLanguage G).BoundedFormula α n) :
    letI := convexStructure O L
    ∀ (z : α → O) (xs : Fin n → O),
      (translateResidueFormula F term φ).Realize (Subtype.val ∘ z) (Subtype.val ∘ xs) ↔
        φ.Realize (IsLocalRing.residue O ∘ z) (IsLocalRing.residue O ∘ xs) := by
  letI := convexStructure O L
  letI := residueLinearOrder O hO
  induction φ with
  | falsum => intros; rfl
  | equal x y =>
    intro z xs
    obtain ⟨hx, hx'⟩ := realize_residueTerm O term hterm x (Sum.elim z xs)
    obtain ⟨hy, hy'⟩ := realize_residueTerm O term hterm y (Sum.elim z xs)
    simp only [comp_sumElim] at hx hx' hy hy'
    rw [translateResidueFormula,
      realize_residueEqBoundedFormula O hF.toInterpretsFieldTerms _ _ _ _ hx hy, hx', hy']
    have hres : IsLocalRing.residue O ∘ Sum.elim z xs =
        Sum.elim (IsLocalRing.residue O ∘ z) (IsLocalRing.residue O ∘ xs) :=
      comp_sumElim (IsLocalRing.residue O) z xs
    rw [hres]
    rfl
  | rel r args =>
    cases r
    intro z xs
    obtain ⟨hx, hx'⟩ := realize_residueTerm O term hterm (args 0) (Sum.elim z xs)
    obtain ⟨hy, hy'⟩ := realize_residueTerm O term hterm (args 1) (Sum.elim z xs)
    simp only [comp_sumElim] at hx hx' hy hy'
    rw [translateResidueFormula,
      realize_residueLEBoundedFormula O hO hF _ _ _ _ hx hy, hx', hy']
    change _ ↔ Structure.RelMap (L := OrderedFunctionalLanguage G) FunctionalOrder.le _
    have hres : IsLocalRing.residue O ∘ Sum.elim z xs =
        Sum.elim (IsLocalRing.residue O ∘ z) (IsLocalRing.residue O ∘ xs) :=
      comp_sumElim (IsLocalRing.residue O) z xs
    rw [horder, hres]
  | imp φ ψ ihφ ihψ =>
    intro z xs
    simp only [translateResidueFormula, BoundedFormula.realize_imp, ihφ z xs, ihψ z xs]
  | @all n φ ih =>
    intro z xs
    simp only [translateResidueFormula, BoundedFormula.realize_all, BoundedFormula.realize_imp,
      realize_valuationRingBoundedFormula O, Term.realize_var, Sum.elim_inr, Fin.snoc_last]
    constructor
    · intro h r
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := O) r
      rw [← Fin.comp_snoc]
      apply (ih z (Fin.snoc xs x)).mp
      rw [Fin.comp_snoc]
      exact h x x.property
    · intro h x hx
      let y : O := ⟨x, hx⟩
      rw [← show (y : K) = x from rfl, ← Fin.comp_snoc]
      apply (ih z (Fin.snoc xs y)).mpr
      rw [Fin.comp_snoc]
      exact h (IsLocalRing.residue O y)

/-- A primitive of the full residue language is interpreted using its
defining graph in the continuous sublanguage. The formula returns zero
when any input is outside the embedded residue field. -/
noncomputable def translatedResidueGraph (F : OrderedFieldTerms (convexLanguage L))
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m)) {n : ℕ}
    (graph : (OrderedFunctionalLanguage G).Formula (Option (Fin n))) :
    (convexLanguage L).Formula (Option (Fin n)) :=
  let inputs := Formula.iInf fun i => residueFormula F.toFieldTerms (.var (some i))
  (inputs ⊓ (residueFormula F.toFieldTerms (.var none) ⊓ translateResidueFormula F term graph)) ⊔
    (inputs.not ⊓ (Term.var none).equal (F.zero.relabel Empty.elim))

set_option linter.style.haveILetI false in
theorem realize_translatedResidueGraph [LinearOrder K] [IsStrictOrderedRing K]
    (hO : IsOrderConvex O) (F : OrderedFieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m)) (hterm : ResidueTermPresentation O term)
    (horder : letI := residueLinearOrder O hO
      ∀ z : Fin 2 → Residue O,
        Structure.RelMap (L := OrderedFunctionalLanguage G) FunctionalOrder.le z ↔ z 0 ≤ z 1)
    {n : ℕ} (graph : (OrderedFunctionalLanguage G).Formula (Option (Fin n)))
    (f : (Fin n → Residue O) → Residue O) (hgraph : DefinesTotalFunction graph f)
    (v : Option (Fin n) → K) :
    letI := convexStructure O L
    (translatedResidueGraph F term graph).Realize v ↔
      rv O (v none) = extendResidueOperation O f (fun i => rv O (v (some i))) := by
  classical
  letI := convexStructure O L
  have hzero : F.zero.realize (v ∘ Empty.elim) = 0 :=
    Subsingleton.elim (v ∘ Empty.elim) (Empty.elim : Empty → K) ▸ hF.zero
  simp only [translatedResidueGraph, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_equal, Formula.realize_not, Term.realize_var,
    realize_residueFormula O hF.toInterpretsFieldTerms, Term.realize_relabel, hzero]
  let args (i : Fin n) := rv O (v (some i))
  change ((∀ i, args i ∈ Set.range (residueRV O)) ∧
      rv O (v none) ∈ Set.range (residueRV O) ∧ Formula.Realize (translateResidueFormula F term graph) v) ∨
      ((¬∀ i, args i ∈ Set.range (residueRV O)) ∧ v none = 0) ↔
    rv O (v none) = extendResidueOperation O f args
  by_cases hargs : ∀ i, args i ∈ Set.range (residueRV O)
  · rw [extendResidueOperation_of_mem_range O f hargs]
    rw [eq_true hargs, true_and, not_true_eq_false, false_and, or_false]
    by_cases hout : rv O (v none) ∈ Set.range (residueRV O)
    · have hv (i : Option (Fin n)) : rv O (v i) ∈ Set.range (residueRV O) := by
        cases i with
        | none => exact hout
        | some i => exact hargs i
      let z (i : Option (Fin n)) : O := ⟨v i, mem_ring_of_rv_mem_residue O (hv i)⟩
      have hz (i : Option (Fin n)) :
          IsLocalRing.residue O (z i) = rvResidue O (rv O (v i)) := by
        rw [rvResidue_rv, totalResidue_of_mem O (z i).property]
      have hf : Formula.Realize (translateResidueFormula F term graph) v ↔
          f (rvResidue O ∘ args) = IsLocalRing.residue O (z none) := by
        let empty : Fin 0 → O := Fin.elim0
        have h := realize_translateResidueFormula O hO F hF term hterm horder graph z empty
        have hval : (Subtype.val ∘ z) = v := rfl
        rw [hval] at h
        have h' : Formula.Realize (translateResidueFormula F term graph) v ↔
            graph.Realize (IsLocalRing.residue O ∘ z) := by
          rw [realize_formula_with_empty_tuple _ _ (Subtype.val ∘ empty),
            realize_formula_with_empty_tuple _ _ (IsLocalRing.residue O ∘ empty)]
          exact h
        rw [h', hgraph.realize_iff]
        rw [show (IsLocalRing.residue O ∘ z) ∘ some = rvResidue O ∘ args from
          funext fun i => hz (some i)]
        rfl
      have heq : rv O (v none) = residueRV O (IsLocalRing.residue O (z none)) :=
        (congrArg (residueRV O) (hz none)).trans
          (residueRV_rvResidue_of_mem_range O hout) |>.symm
      simp only [hout, true_and, hf]
      rw [heq, (residueRV_injective O).eq_iff, eq_comm]
    · simp only [hout, false_and, false_iff]
      exact fun h => hout ⟨_, h.symm⟩
  · obtain ⟨i, hi⟩ := not_forall.mp hargs
    rw [extendResidueOperation_off_residue O f ⟨i, hi⟩, rv_eq_zero_iff]
    simp only [hargs, false_and, not_false_eq_true, true_and, false_or]

/-- The uniform formula for each residue primitive, with its variables
indexed by the sorted signature. -/
noncomputable def translatedResidueGraphFamily
    (F : OrderedFieldTerms (convexLanguage L))
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m))
    (definition : ∀ {m}, L.Functions m → (OrderedFunctionalLanguage G).Formula (Option (Fin m)))
    {n : ℕ} (f : L.Functions n) :
    (convexLanguage L).Formula (Option (Fin (List.replicate n TCsort.rv).length)) :=
  (translatedResidueGraph F term (definition f)).relabel (Option.map (Fin.cast List.length_replicate.symm))

universe e

set_option linter.style.haveILetI false in
/-- Given the continuous presentation and the defining graphs for the
extra symbols, all operations and relations of the canonical RV expansion
are interpreted by a single assignment of valued-field formulas. -/
noncomputable def realizesCanonicalInterpretationOfResidueDefinitions
    [LinearOrder K] [IsStrictOrderedRing K] [L.Structure (Residue O)] {E : Type e}
    (hO : IsOrderConvex O) (F : OrderedFieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsOrderedFieldTerms (A := K) F)
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m)) (hterm : ResidueTermPresentation O term)
    (horder : letI := residueLinearOrder O hO
      ∀ z : Fin 2 → Residue O,
        Structure.RelMap (L := OrderedFunctionalLanguage G) FunctionalOrder.le z ↔ z 0 ≤ z 1)
    (definition : ∀ {m}, L.Functions m → (OrderedFunctionalLanguage G).Formula (Option (Fin m)))
    (hdefinition : ∀ {n} (f : L.Functions n), DefinesTotalFunction (definition f)
      (Structure.funMap f : (Fin n → Residue O) → Residue O))
    (power : E → (convexLanguage L).Formula (Fin 2))
    (g : E → PositiveField K →* PositiveField K) (P : E → RV0 O → RV0 O)
    (hpower : letI := convexStructure O L
      ∀ i (v : Fin 2 → K), (power i).Realize v ↔ totalFieldPower (g i) (v 0) = v 1)
    (hP : ∀ i, AgreesWithFieldPower O (g i) (P i))
    (hP₀ : ∀ i t, ¬IsPositiveRV O t → P i t = 0) :
    letI := convexStructure O L
    RealizesQuotientInterpretation
      (canonicalQuotientInterpretation F (translatedResidueGraphFamily F term definition) power)
      (A := K) (canonicalStructure O hO P) := by
  letI := convexStructure O L
  apply realizesCanonicalQuotientInterpretation O hO F hF
    (translatedResidueGraphFamily F term definition) power g P hpower hP hP₀
  intro n f v
  rw [translatedResidueGraphFamily, Formula.realize_relabel,
    realize_translatedResidueGraph O hO F hF term hterm horder _ _ (hdefinition f)]
  have hargs : (fun i : Fin n => rv O (v (some (Fin.cast List.length_replicate.symm i)))) =
      rv O ∘ homogeneousArgs (X := fun _ => K) (s := .rv) (fun i => v (some i)) := by
    funext i
    rw [Function.comp_apply, homogeneousArgs_const]
  change (rv O (v none) = extendResidueOperation O (Structure.funMap f)
    (fun i : Fin n => rv O (v (some (Fin.cast List.length_replicate.symm i))))) ↔ _
  rw [hargs]

universe u' v'

private theorem languageStructure_eq {J : Language.{u', v'}} {A : Type*}
    (M N : J.Structure A)
    (functions : ∀ {n} (f : J.Functions n) (x : Fin n → A), M.funMap f x = N.funMap f x)
    (relations : ∀ {n} (r : J.Relations n) (x : Fin n → A), M.RelMap r x ↔ N.RelMap r x) :
    M = N := by
  cases M
  cases N
  congr 1
  · funext n f x
    exact functions f x
  · funext n r x
    exact propext (relations r x)

omit [(OrderedFunctionalLanguage G).Structure (Residue O)] in
/-- Surjectivity of reduction fixes the interpretations of all continuous
primitive functions, and the quotient order fixes the relation. -/
theorem continuousResidueStructure_unique [LinearOrder K] [IsStrictOrderedRing K]
    (hO : IsOrderConvex O) (M N : (OrderedFunctionalLanguage G).Structure (Residue O))
    (term : ∀ {m}, G m → (convexLanguage L).Term (Fin m))
    (hM : @ResidueTermPresentation L G K _ _ O M term)
    (hN : @ResidueTermPresentation L G K _ _ O N term)
    (hMOrder : letI := residueLinearOrder O hO
      ∀ x : Fin 2 → Residue O, M.RelMap FunctionalOrder.le x ↔ x 0 ≤ x 1)
    (hNOrder : letI := residueLinearOrder O hO
      ∀ x : Fin 2 → Residue O, N.RelMap FunctionalOrder.le x ↔ x 0 ≤ x 1) : M = N := by
  apply languageStructure_eq M N
  · intro n f x
    have hsurj (i : Fin n) : ∃ y : O, IsLocalRing.residue O y = x i :=
      IsLocalRing.residue_surjective (x i)
    choose y hy using hsurj
    have hxy : IsLocalRing.residue O ∘ y = x := funext hy
    obtain ⟨hm, hmf⟩ := hM f y
    obtain ⟨hn, hnf⟩ := hN f y
    rw [hxy] at hmf hnf
    exact hmf.symm.trans hnf
  · intro n r x
    cases r
    exact (hMOrder x).trans (hNOrder x).symm

omit [L.Structure K] in
/-- The graphs in a common continuous residue reduct fix the interpretations
of the additional function symbols of the full language. -/
theorem residueStructure_eq_of_reduct_definitions
    (M N : L.Structure (Residue O))
    (definition : ∀ {n}, L.Functions n → (OrderedFunctionalLanguage G).Formula (Option (Fin n)))
    (hM : ∀ {n} (f : L.Functions n), DefinesTotalFunction (definition f) (M.funMap f))
    (hN : ∀ {n} (f : L.Functions n), DefinesTotalFunction (definition f) (N.funMap f))
    (hrel : ∀ {n} (r : L.Relations n) (x : Fin n → Residue O), M.RelMap r x ↔ N.RelMap r x) :
    M = N :=
  languageStructure_eq M N (fun f x => congrFun ((hM f).unique (hN f)) x) hrel

end GeneralizedEuler.Section2
