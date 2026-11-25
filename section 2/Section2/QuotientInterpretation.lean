module

public import Section2.TaggedTheory
public import Section2.SortedModelTheory
public import Section2.ConvexLanguage
public import Mathlib.ModelTheory.Definability

/-! First-order interpretation of the two sorts by field representatives,
as used for completeness in Theorem 2.14. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w u' v' z a b

variable {L : Language.{u, v}} {E : Type w} {J : Language.{u', v'}}

/-- Formulas of the interpreting language for quotient equality,
the operation graphs, and the relations. -/
structure QuotientInterpretation (J : Language.{u', v'}) (L : Language.{u, v}) (E : Type w) where
  equal : TCsort → J.Formula (Fin 2)
  function : ∀ {ss s}, FunctionSymbol L E ss s → J.Formula (Option (Fin ss.length))
  relation : ∀ {ss}, RelationSymbol L ss → J.Formula (Fin ss.length)

variable (I : QuotientInterpretation J L E)

/-- Each sort consists of equivalence classes of representatives, and
the interpreting formulas give the induced operations on the classes. -/
structure RealizesQuotientInterpretation {A : Type b} [J.Structure A] {X : TCsort → Type z}
    (M : SortedStructure L E X) where
  rep : ∀ s, A → X s
  surjective : ∀ s, Function.Surjective (rep s)
  equal : ∀ s (v : Fin 2 → A), (I.equal s).Realize v ↔ rep s (v 0) = rep s (v 1)
  function : ∀ {ss s} (f : FunctionSymbol L E ss s) (v : Option (Fin ss.length) → A),
    (I.function f).Realize v ↔ rep s (v none) = M.funMap f (fun i => rep _ (v (some i)))
  relation : ∀ {ss} (r : RelationSymbol L ss) (v : Fin ss.length → A),
    (I.relation r).Realize v ↔ M.relMap r (fun i => rep _ (v i))

/-- The graph of a term, with a variable for a representative of its
value. The graph may have several representatives for the same value. -/
def QuotientInterpretation.termGraph (I : QuotientInterpretation J L E)
    {Var : TCsort → Type a} :
    {s : TCsort} → SortedTerm L E Var s → J.Formula (TaggedVar Var ⊕ Unit)
  | s, .var x => (I.equal s).relabel (Fin.cases (.inr ()) (fun _ => .inl ⟨s, x⟩))
  | _, @SortedTerm.app _ _ _ ss _ f ts =>
    Formula.iExs (Fin ss.length)
      ((Formula.iInf fun i => (termGraph I (ts i)).relabel
        (Sum.elim (fun a => .inl (.inl a)) (fun _ => .inr i))) ⊓
        ((I.function f).relabel fun
          | none => .inl (.inr ())
          | some i => .inr i))

namespace RealizesQuotientInterpretation

variable {A : Type b} [J.Structure A] {X : TCsort → Type z}
  {M : SortedStructure L E X} {I}
  (R : RealizesQuotientInterpretation I (A := A) M)

def assignment {Var : TCsort → Type a} (v : TaggedVar Var → A) : ∀ s, Var s → X s :=
  fun s x => R.rep s (v ⟨s, x⟩)

theorem assignment_apply {Var : TCsort → Type a} (v : TaggedVar Var → A) (s : TCsort) (x : Var s) :
    R.assignment v s x = R.rep s (v ⟨s, x⟩) := by rfl

private theorem appGraphAssignment {α β : Type*} (v : α → A) (u : Unit → A)
    (z : β → A) (i : β) :
    Sum.elim (Sum.elim v u) z ∘ Sum.elim (fun a => .inl (.inl a)) (fun _ : Unit => .inr i) =
      Sum.elim v (fun _ : Unit => z i) := by
  funext a
  cases a <;> rfl

theorem realize_termGraph {Var : TCsort → Type a} {s : TCsort} (t : SortedTerm L E Var s) :
    ∀ (v : TaggedVar Var → A) (y : A),
      (I.termGraph t).Realize (Sum.elim v (fun _ => y)) ↔
        R.rep s y = t.realize M (R.assignment v) := by
  induction t with
  | var x =>
    intro v y
    rw [QuotientInterpretation.termGraph, Formula.realize_relabel, R.equal]
    rfl
  | app f ts ih =>
    rename_i ss _
    intro v y
    simp only [QuotientInterpretation.termGraph, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_iInf, Formula.realize_relabel, R.function, SortedTerm.realize,
      appGraphAssignment]
    change (∃ z : Fin ss.length → A,
      (∀ i, (I.termGraph (ts i)).Realize (Sum.elim v (fun _ => z i))) ∧
      R.rep _ y = M.funMap f (fun i => R.rep _ (z i))) ↔
        R.rep _ y = M.funMap f (fun i => (ts i).realize M (R.assignment v))
    constructor
    · rintro ⟨z, hz, heq⟩
      exact heq.trans (congrArg (M.funMap f) (funext fun i => (ih i v (z i)).mp (hz i)))
    · intro h
      have reify (i) : ∃ z, R.rep _ z = (ts i).realize M (R.assignment v) :=
        R.surjective _ _
      choose z hz using reify
      exact ⟨z, fun i => (ih i v (z i)).mpr (hz i),
        h.trans (congrArg (M.funMap f) (funext hz)).symm⟩

end RealizesQuotientInterpretation

private def graphAt {α β : Type*} (f : J.Formula (α ⊕ Unit)) (b : β) :
    J.Formula (α ⊕ β) :=
  f.relabel (Sum.elim Sum.inl (fun _ => Sum.inr b))

def QuotientInterpretation.translate (I : QuotientInterpretation J L E) :
    {Var : TCsort → Type a} → SortedFormula L E Var → J.Formula (TaggedVar Var)
  | _, .falsum => ⊥
  | _, @SortedFormula.equal _ _ _ s t t' =>
    Formula.iExs (Fin 2)
      (graphAt (I.termGraph t) (0 : Fin 2) ⊓
        (graphAt (I.termGraph t') (1 : Fin 2) ⊓ (I.equal s).relabel Sum.inr))
  | _, @SortedFormula.rel _ _ _ ss r ts =>
    Formula.iExs (Fin ss.length)
      ((Formula.iInf fun i => graphAt (I.termGraph (ts i)) i) ⊓ (I.relation r).relabel Sum.inr)
  | _, .imp φ ψ => (translate I φ).imp (translate I ψ)
  | _, .all s φ => Formula.iAlls Unit ((translate I φ).relabel (splitAddedVar s))

namespace RealizesQuotientInterpretation

variable {A : Type b} [J.Structure A] {X : TCsort → Type z}
  {M : SortedStructure L E X} {I} (R : RealizesQuotientInterpretation I (A := A) M)

private theorem assignment_split {Var : TCsort → Type a} (v : TaggedVar Var → A)
    (s : TCsort) (u : Unit → A) :
    R.assignment (Sum.elim v u ∘ splitAddedVar s) =
      extendSortedAssignment (R.assignment v) (R.rep s (u ())) := by
  funext t x
  rcases x with x | h
  · rfl
  · obtain ⟨h⟩ := h
    subst t
    rfl

private theorem graphAtAssignment {α β : Type*} (v : α → A) (z : β → A) (i : β) :
    Sum.elim v z ∘ Sum.elim Sum.inl (fun _ : Unit => .inr i) =
      Sum.elim v (fun _ : Unit => z i) := by
  funext a
  cases a <;> rfl

theorem realize_translate {Var : TCsort → Type a} (φ : SortedFormula L E Var) :
    ∀ v : TaggedVar Var → A, (I.translate φ).Realize v ↔ φ.realize M (R.assignment v) := by
  induction φ with
  | falsum => intro v; rfl
  | equal t t' =>
    rename_i s
    intro v
    simp only [QuotientInterpretation.translate, Formula.realize_iExs, Formula.realize_inf,
      graphAt, Formula.realize_relabel, R.equal, SortedFormula.realize, graphAtAssignment]
    change (∃ z : Fin 2 → A, (I.termGraph t).Realize (Sum.elim v (fun _ => z 0)) ∧
      (I.termGraph t').Realize (Sum.elim v (fun _ => z 1)) ∧ R.rep s (z 0) = R.rep s (z 1)) ↔ _
    simp only [R.realize_termGraph]
    constructor
    · rintro ⟨z, ht, ht', h⟩
      exact ht.symm.trans (h.trans ht')
    · intro h
      obtain ⟨a, ha⟩ := R.surjective _ (t.realize M (R.assignment v))
      obtain ⟨b, hb⟩ := R.surjective _ (t'.realize M (R.assignment v))
      let z : Fin 2 → A := fun i => if i = 0 then a else b
      have h0 : z 0 = a := by simp [z]
      have h1 : z 1 = b := by simp [z]
      refine ⟨z, ?_⟩
      rw [h0, h1]
      exact ⟨ha, hb, ha.trans (h.trans hb.symm)⟩
  | rel r ts =>
    rename_i ss
    intro v
    simp only [QuotientInterpretation.translate, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_iInf, graphAt, Formula.realize_relabel, R.relation, SortedFormula.realize,
      graphAtAssignment]
    change (∃ z : Fin ss.length → A,
      (∀ i, (I.termGraph (ts i)).Realize (Sum.elim v fun _ => z i)) ∧
      M.relMap r (fun i => R.rep _ (z i))) ↔ _
    simp only [R.realize_termGraph]
    constructor
    · rintro ⟨z, hz, h⟩
      rwa [funext hz] at h
    · intro h
      have reify (i) : ∃ y, R.rep _ y = (ts i).realize M (R.assignment v) :=
        R.surjective _ _
      choose z hz using reify
      exact ⟨z, hz, funext hz ▸ h⟩
  | imp φ ψ ihφ ihψ =>
    intro v
    simp only [QuotientInterpretation.translate, Formula.realize_imp, ihφ, ihψ,
      SortedFormula.realize]
  | all s φ ih =>
    intro v
    simp only [QuotientInterpretation.translate, Formula.realize_iAlls, Formula.realize_relabel,
      ih, R.assignment_split, SortedFormula.realize]
    constructor
    · intro h x
      obtain ⟨y, hy⟩ := R.surjective s x
      exact hy ▸ h (fun _ => y)
    · intro h u
      exact h (R.rep s (u ()))

end RealizesQuotientInterpretation

def QuotientInterpretation.sentence (I : QuotientInterpretation J L E)
    (φ : SortedSentence L E) : J.Sentence :=
  (I.translate φ).relabel (fun a => a.2)

theorem RealizesQuotientInterpretation.realize_sentence {A : Type b} [J.Structure A]
    {X : TCsort → Type z} {M : SortedStructure L E X} {I : QuotientInterpretation J L E}
    (R : RealizesQuotientInterpretation I (A := A) M) (φ : SortedSentence L E) :
    A ⊨ (I.sentence φ : J.Sentence) ↔ φ.realize M := by
  rw [Sentence.Realize, QuotientInterpretation.sentence, Formula.realize_relabel,
    R.realize_translate, SortedSentence.realize]
  have h : R.assignment (default ∘ fun a : TaggedVar (fun _ => Empty) => a.2) =
      (fun _ => Empty.elim) := by
    funext s x
    exact x.elim
  rw [h]

/-- A sorted definable set pulls back to a definable set of representatives.
The parameters of the pullback can be taken from a specified set containing
representatives of all the named sorted parameters. -/
theorem RealizesQuotientInterpretation.definable_preimage
    {A : Type b} [J.Structure A] {X : TCsort → Type z}
    {M : SortedStructure L E X} {I : QuotientInterpretation J L E}
    (R : RealizesQuotientInterpretation I (A := A) M)
    {Var : TCsort → Type a} {S : ∀ s, Set (X s)} {B : Set A}
    {D : Set (∀ s, Var s → X s)}
    (hD : SortedDefinableOver M S D)
    (hrep : ∀ s (x : S s), ∃ y : B, R.rep s y.val = x.val) :
    B.Definable J ((R.assignment : (TaggedVar Var → A) → _) ⁻¹' D) := by
  obtain ⟨φ, hφ⟩ := hD
  choose lift hlift using hrep
  let ren : TaggedVar (fun s => (S s : Type z) ⊕ Var s) → B ⊕ TaggedVar Var := fun
    | ⟨s, .inl x⟩ => .inl (lift s x)
    | ⟨s, .inr x⟩ => .inr ⟨s, x⟩
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨(I.translate φ).relabel ren, ?_⟩
  ext v
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Formula.realize_relabel, R.realize_translate, hφ]
  have h : R.assignment (Sum.elim Subtype.val v ∘ ren) =
      (fun s => Sum.elim Subtype.val (R.assignment v s)) := by
    funext s x
    rcases x with x | x
    · exact hlift s x
    · rfl
  rw [h]

/-- In the convention of §2.1, surjectivity of the representative maps
supplies all the parameters needed for the pullback. -/
theorem RealizesQuotientInterpretation.definable_preimage_with_all_parameters
    {A : Type b} [J.Structure A] {X : TCsort → Type z}
    {M : SortedStructure L E X} {I : QuotientInterpretation J L E}
    (R : RealizesQuotientInterpretation I (A := A) M)
    {Var : TCsort → Type a} {S : ∀ s, Set (X s)} {D : Set (∀ s, Var s → X s)}
    (hD : SortedDefinableOver M S D) :
    (Set.univ : Set A).Definable J ((R.assignment : (TaggedVar Var → A) → _) ⁻¹' D) := by
  apply R.definable_preimage hD
  intro s x
  obtain ⟨y, hy⟩ := R.surjective s x.val
  exact ⟨⟨y, Set.mem_univ _⟩, hy⟩

/-- Completeness descends to the interpreted structure when the
interpretation is uniform in the models of the underlying theory. -/
theorem sortedSentence_iff_of_complete_interpreted_theory
    {T : J.Theory} (hT : T.IsComplete)
    {A B : Type*} [J.Structure A] [Nonempty A] [A ⊨ T]
      [J.Structure B] [Nonempty B] [B ⊨ T]
    {X Y : TCsort → Type*} {M : SortedStructure L E X} {N : SortedStructure L E Y}
    (RM : RealizesQuotientInterpretation I (A := A) M)
    (RN : RealizesQuotientInterpretation I (A := B) N) (φ : SortedSentence L E) :
    φ.realize M ↔ φ.realize N := by
  rw [← RM.realize_sentence, ← RN.realize_sentence]
  exact (hT.realize_sentence_iff (I.sentence φ) A).trans
    (hT.realize_sentence_iff (I.sentence φ) B).symm

/-- Completeness transfers to all presentations isomorphic to the
uniformly interpreted expansions. -/
theorem sortedSentence_iff_of_complete_interpreted_presentations
    {T : J.Theory} (hT : T.IsComplete)
    {A B : Type*} [J.Structure A] [Nonempty A] [A ⊨ T]
      [J.Structure B] [Nonempty B] [B ⊨ T]
    {X Y U V : TCsort → Type*}
    {M : SortedStructure L E X} {N : SortedStructure L E Y}
      {M' : SortedStructure L E U} {N' : SortedStructure L E V}
    (RM : RealizesQuotientInterpretation I (A := A) M)
    (RN : RealizesQuotientInterpretation I (A := B) N)
    (i : SortedIsomorphism M M') (j : SortedIsomorphism N N') (φ : SortedSentence L E) :
    φ.realize M' ↔ φ.realize N' :=
  (i.realize_sentence φ).symm.trans
    ((sortedSentence_iff_of_complete_interpreted_theory I hT RM RN φ).trans (j.realize_sentence φ))

/-- When all named elements have common field representatives, QE in
the valued-field reduct transfers their full sorted type. -/
theorem sortedFormula_iff_of_common_field_representatives
    {T : J.Theory} (hT : EliminatesQuantifiers T)
    {A B C : Type*} [J.Structure A] [J.Structure B] [Nonempty B] [B ⊨ T]
      [J.Structure C] [Nonempty C] [C ⊨ T]
    {X Y : TCsort → Type*} {M : SortedStructure L E X} {N : SortedStructure L E Y}
    (RM : RealizesQuotientInterpretation I (A := B) M)
    (RN : RealizesQuotientInterpretation I (A := C) N)
    (p : A ↪[J] B) (q : A ↪[J] C) {Var : TCsort → Type a}
    (representatives : TaggedVar Var → A) (φ : SortedFormula L E Var) :
    φ.realize M (RM.assignment (p ∘ representatives)) ↔
      φ.realize N (RN.assignment (q ∘ representatives)) := by
  rw [← RM.realize_translate, ← RN.realize_translate]
  exact partialElementaryOfQE_anyVar hT p q (I.translate φ) representatives

/-- Two realizations of the same quotient interpretation on a common
field structure are isomorphic. The isomorphism sends each class of a
representative to the class of that same representative. -/
theorem exists_sortedIsomorphism_of_common_interpretation
    {A : Type*} [J.Structure A] {X Y : TCsort → Type*}
    {M : SortedStructure L E X} {N : SortedStructure L E Y}
    (RM : RealizesQuotientInterpretation I (A := A) M)
    (RN : RealizesQuotientInterpretation I (A := A) N) :
    ∃ e : SortedIsomorphism M N, ∀ s a, e.toEmbedding s (RM.rep s a) = RN.rep s a := by
  let pre (s : TCsort) (x : X s) : A := (RM.surjective s x).choose
  have hpre (s : TCsort) (x : X s) : RM.rep s (pre s x) = x := (RM.surjective s x).choose_spec
  have compare (s : TCsort) (a b : A) : RM.rep s a = RM.rep s b ↔ RN.rep s a = RN.rep s b :=
    ((RM.equal s ![a, b]).symm.trans (RN.equal s ![a, b]))
  let map (s : TCsort) (x : X s) := RN.rep s (pre s x)
  have onRep (s : TCsort) (a : A) : map s (RM.rep s a) = RN.rep s a :=
    (compare s _ a).mp (hpre s _)
  have hInjective (s : TCsort) : Function.Injective (map s) := by
    intro x y he
    exact (hpre s x).symm.trans ((compare s _ _).mpr he |>.trans (hpre s y))
  let e : SortedIsomorphism M N :=
    { toEmbedding := fun s => ⟨map s, hInjective s⟩
      map_fun := by
        intro ss s f xs
        let v : Option (Fin ss.length) → A := fun
          | none => pre s (M.funMap f xs)
          | some j => pre (ss.get j) (xs j)
        have hRep : (fun j => RM.rep (ss.get j) (v (some j))) = xs :=
          funext fun j => hpre (ss.get j) (xs j)
        have h : (I.function f).Realize v := (RM.function f v).mpr (by
          rw [hRep]
          exact hpre s _)
        exact (RN.function f v).mp h
      map_rel := by
        intro ss r xs
        let v (i : Fin ss.length) := pre (ss.get i) (xs i)
        have hRep : (fun j => RM.rep (ss.get j) (v j)) = xs :=
          funext fun j => hpre (ss.get j) (xs j)
        have h := (RN.relation r v).symm.trans (RM.relation r v)
        rwa [hRep] at h
      surjective := by
        intro s y
        obtain ⟨a, rfl⟩ := RN.surjective s y
        exact ⟨RM.rep s a, onRep s a⟩ }
  exact ⟨e, onRep⟩

/-- Transport a substructure using common field representatives. The
interpreting formulas and field QE give preservation of all primitives
on the transported representatives, even when the common field
substructure does not itself model the valued-field theory. -/
theorem exists_sortedEmbedding_of_common_field_representatives
    {T : J.Theory} (hT : EliminatesQuantifiers T)
    {A B C : Type*} [J.Structure A] [J.Structure B] [Nonempty B] [B ⊨ T]
      [J.Structure C] [Nonempty C] [C ⊨ T]
    {X Y : TCsort → Type*} {M : SortedStructure L E X} {N : SortedStructure L E Y}
    (RM : RealizesQuotientInterpretation I (A := B) M)
    (RN : RealizesQuotientInterpretation I (A := C) N)
    (p : A ↪[J] B) (q : A ↪[J] C) (S : SortedSubstructure M)
    (r : ∀ s, S.carrier s → A)
    (hr : ∀ s (x : S.carrier s), RM.rep s (p (r s x)) = x.val) :
    ∃ e : SortedEmbedding S.structureOn N,
      ∀ s (x : S.carrier s), e.toEmbedding s x = RN.rep s (q (r s x)) := by
  let representatives : TaggedVar (fun s => S.carrier s) → A := fun a => r a.1 a.2
  let map (s : TCsort) (x : S.carrier s) := RN.rep s (q (r s x))
  have hLeft : RM.assignment (p ∘ representatives) = fun _ x => x.val := by
    funext s x
    rw [RealizesQuotientInterpretation.assignment_apply]
    exact hr s x
  have hRight : RN.assignment (q ∘ representatives) = map := by
    funext s x
    rw [RealizesQuotientInterpretation.assignment_apply]
    rfl
  have transfer (φ : SortedFormula L E (fun s => S.carrier s)) :
      φ.realize M (fun _ x => x.val) ↔ φ.realize N map := by
    have h := sortedFormula_iff_of_common_field_representatives I hT RM RN p q representatives φ
    rwa [hLeft, hRight] at h
  let e : SortedEmbedding S.structureOn N := {
    toEmbedding := fun s => ⟨map s, fun x y he => Subtype.ext
      ((transfer (.equal (.var x) (.var y))).mpr he)⟩
    map_fun := fun f xs =>
      (transfer (.equal (.var (S.structureOn.funMap f xs)) (.app f (fun i => .var (xs i))))).mp rfl
    map_rel := fun f xs => (transfer (.rel f fun i => .var (xs i))).symm }
  exact ⟨e, fun _ _ => rfl⟩

end GeneralizedEuler.Section2
