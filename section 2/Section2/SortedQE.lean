module

public import Section2.SortedTypes
public import Section2.GeneratedSubstructure

/-! The compactness step of the Shoenfield test used in Theorem 2.16. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w a

variable {L : Language.{u, v}} {E : Type w} {Var : TCsort → Type a}

namespace SortedFormula

def neg (φ : SortedFormula L E Var) : SortedFormula L E Var := .imp φ .falsum

theorem neg_isQF {φ : SortedFormula L E Var} (hφ : φ.IsQF) : φ.neg.IsQF :=
  .imp hφ .falsum

@[simp]
theorem realize_neg {X : TCsort → Type*} (M : SortedStructure L E X)
    (x : ∀ s, Var s → X s) (φ : SortedFormula L E Var) :
    φ.neg.realize M x ↔ ¬φ.realize M x := Iff.rfl

@[expose]
def conjunction (φ ψ : SortedFormula L E Var) : SortedFormula L E Var :=
  (.imp φ ψ.neg : SortedFormula L E Var).neg

@[expose]
def disjunction (φ ψ : SortedFormula L E Var) : SortedFormula L E Var :=
  .imp φ.neg ψ

theorem realize_conjunction {X : TCsort → Type*} (M : SortedStructure L E X)
    (x : ∀ s, Var s → X s) (φ ψ : SortedFormula L E Var) :
    (φ.conjunction ψ).realize M x ↔ φ.realize M x ∧ ψ.realize M x := by
  classical
  simp only [conjunction, realize_neg, SortedFormula.realize, not_imp, not_not]

theorem realize_disjunction {X : TCsort → Type*} (M : SortedStructure L E X)
    (x : ∀ s, Var s → X s) (φ ψ : SortedFormula L E Var) :
    (φ.disjunction ψ).realize M x ↔ φ.realize M x ∨ ψ.realize M x := by
  classical
  simp only [disjunction, SortedFormula.realize, realize_neg, ← or_iff_not_imp_left]

def allOf (l : List (SortedFormula L E Var)) : SortedFormula L E Var :=
  l.foldr conjunction (.neg .falsum)

def anyOf (l : List (SortedFormula L E Var)) : SortedFormula L E Var :=
  l.foldr disjunction .falsum

private theorem allOf_isQF (l : List (SortedFormula L E Var)) (h : ∀ ψ ∈ l, ψ.IsQF) :
    (allOf l).IsQF := by
  induction l with
  | nil => exact neg_isQF .falsum
  | cons ψ l ih =>
    exact neg_isQF (.imp (h ψ (List.mem_cons_self ..))
      (neg_isQF (ih (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)))))

private theorem anyOf_isQF (l : List (SortedFormula L E Var)) (h : ∀ ψ ∈ l, ψ.IsQF) :
    (anyOf l).IsQF := by
  induction l with
  | nil => exact .falsum
  | cons ψ l ih =>
    exact .imp (neg_isQF (h ψ (List.mem_cons_self ..)))
      (ih (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)))

theorem realize_allOf {X : TCsort → Type*} (M : SortedStructure L E X)
    (x : ∀ s, Var s → X s) (l : List (SortedFormula L E Var)) :
    (allOf l).realize M x ↔ ∀ ψ ∈ l, ψ.realize M x := by
  classical
  induction l with
  | nil => simp [allOf, SortedFormula.realize]
  | cons ψ l ih =>
    change (conjunction ψ (allOf l)).realize M x ↔ _
    simp only [realize_conjunction, ih, List.forall_mem_cons]

theorem realize_anyOf {X : TCsort → Type*} (M : SortedStructure L E X)
    (x : ∀ s, Var s → X s) (l : List (SortedFormula L E Var)) :
    (anyOf l).realize M x ↔ ∃ ψ ∈ l, ψ.realize M x := by
  classical
  induction l with
  | nil => simp [anyOf, SortedFormula.realize]
  | cons ψ l ih =>
    change (disjunction ψ (anyOf l)).realize M x ↔ _
    simp only [realize_disjunction, ih, List.exists_mem_cons_iff]

end SortedFormula

namespace SortedTheory

variable (T : SortedTheory L E)

/-- A model of the sorted theory with a specified tuple. -/
structure PointedModel (Var : TCsort → Type a) where
  carrier : TCsort → Type (max u v w a)
  model : SortedStructure L E carrier
  point : ∀ s, Var s → carrier s
  nonempty : ∀ s, Nonempty (carrier s)
  models : ∀ φ ∈ T, φ.realize model

@[expose]
def PointedModel.realizes {T : SortedTheory L E}
    (P : T.PointedModel Var) (φ : SortedFormula L E Var) : Prop :=
  φ.realize P.model P.point

theorem realizable_iff_pointedModel {Δ : Set (SortedFormula L E Var)} :
    T.Realizable Δ ↔ ∃ P : T.PointedModel Var, ∀ φ ∈ Δ, P.realizes φ := by
  constructor
  · rintro ⟨X, M, x, hx, hM, hΔ⟩
    exact ⟨⟨X, M, x, hx, hM⟩, hΔ⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.carrier, P.model, P.point, P.nonempty, P.models, hP⟩

private theorem finite_unrealizable {Δ : Set (SortedFormula L E Var)}
    (h : ¬T.Realizable Δ) :
    ∃ U : Finset (SortedFormula L E Var), (U : Set (SortedFormula L E Var)) ⊆ Δ ∧
      ¬T.Realizable (U : Set (SortedFormula L E Var)) := by
  classical
  by_contra! H
  exact h (T.realizable_of_finite Δ H)

/-- A cover of a formula by formulas that works in every pointed model has
a finite subcover. This is the compactness step for choosing chart templates. -/
theorem exists_finite_formula_cover {I : Type*} (φ : SortedFormula L E Var)
    (charts : I → SortedFormula L E Var)
    (hcover : ∀ P : T.PointedModel Var, P.realizes φ → ∃ i, P.realizes (charts i)) :
    ∃ U : Finset I, ∀ P : T.PointedModel Var, P.realizes φ → ∃ i ∈ U, P.realizes (charts i) := by
  classical
  let negChart (i : I) := (charts i).neg
  let Δ : Set (SortedFormula L E Var) := insert φ (negChart '' Set.univ)
  have hunreal : ¬T.Realizable Δ := by
    rw [T.realizable_iff_pointedModel]
    rintro ⟨P, hP⟩
    obtain ⟨i, hi⟩ := hcover P (hP φ (Set.mem_insert _ _))
    exact (hP (negChart i) (Set.mem_insert_of_mem _ ⟨i, Set.mem_univ _, rfl⟩)) hi
  obtain ⟨V, hV, hVunreal⟩ := T.finite_unrealizable hunreal
  let V' := V.filter (· ≠ φ)
  have hV' : (V' : Set _) ⊆ negChart '' Set.univ := by
    intro ψ hψ
    obtain ⟨hψV, hψφ⟩ := Finset.mem_filter.mp hψ
    exact (Set.mem_insert_iff.mp (hV hψV)).resolve_left hψφ
  obtain ⟨U, _, hU⟩ := Finset.subset_set_image_iff.mp hV'
  refine ⟨U, fun P hP => ?_⟩
  by_contra! hfail
  apply hVunreal
  apply (T.realizable_iff_pointedModel).mpr
  refine ⟨P, fun ψ hψ => ?_⟩
  by_cases hψφ : ψ = φ
  · exact hψφ.symm ▸ hP
  have hImage : ψ ∈ U.image negChart := hU ▸ Finset.mem_filter.mpr ⟨hψ, hψφ⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hImage
  exact hfail i hi

variable {T}

private def qfType (P : T.PointedModel Var) : Set (SortedFormula L E Var) :=
  {ψ | ψ.IsQF ∧ P.realizes ψ}

private theorem agrees_of_realizes_qfType (P Q : T.PointedModel Var)
    (h : ∀ ψ ∈ qfType P, Q.realizes ψ) :
    ∀ ψ : SortedFormula L E Var, ψ.IsQF → (P.realizes ψ ↔ Q.realizes ψ) := by
  intro ψ hψ
  refine ⟨fun hp => h ψ ⟨hψ, hp⟩, ?_⟩
  intro hq
  by_contra hp
  exact (h ψ.neg ⟨SortedFormula.neg_isQF hψ, hp⟩) hq

private def sufficientQF (φ : SortedFormula L E Var) : Set (SortedFormula L E Var) :=
  {ψ | ψ.IsQF ∧ ∀ P : T.PointedModel Var, P.realizes ψ → P.realizes φ}

private theorem exists_sufficientQF {φ : SortedFormula L E Var} (P : T.PointedModel Var)
    (hP : P.realizes φ)
    (hdet : ∀ P Q : T.PointedModel Var,
      (∀ ψ : SortedFormula L E Var, ψ.IsQF → (P.realizes ψ ↔ Q.realizes ψ)) →
      (P.realizes φ ↔ Q.realizes φ)) :
    ∃ ψ ∈ sufficientQF (T := T) φ, P.realizes ψ := by
  classical
  have h : ¬T.Realizable (qfType P ∪ {φ.neg}) := by
    rw [T.realizable_iff_pointedModel]
    rintro ⟨Q, hQ⟩
    have hagree := agrees_of_realizes_qfType P Q (fun ψ hψ => hQ ψ (Or.inl hψ))
    exact (hQ φ.neg (Or.inr rfl)) ((hdet P Q hagree).mp hP)
  obtain ⟨U, hU, hUnreal⟩ := T.finite_unrealizable h
  let V := U.filter (· ∈ qfType P)
  have hV (ψ : SortedFormula L E Var) (hψ : ψ ∈ V.toList) : ψ.IsQF ∧ P.realizes ψ :=
    (Finset.mem_filter.mp (Finset.mem_toList.mp hψ)).2
  let ψ := SortedFormula.allOf V.toList
  refine ⟨ψ, ⟨SortedFormula.allOf_isQF _ (fun χ hχ => (hV χ hχ).1), ?_⟩,
    (SortedFormula.realize_allOf _ _ _).mpr (fun χ hχ => (hV χ hχ).2)⟩
  intro Q hQ
  by_contra hQφ
  apply hUnreal
  apply (T.realizable_iff_pointedModel).mpr
  refine ⟨Q, fun χ hχ => ?_⟩
  rcases hU hχ with hχq | hχn
  · exact (SortedFormula.realize_allOf _ _ _).mp hQ χ
      (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hχ, hχq⟩))
  · have heq : χ = φ.neg := hχn
    exact heq.symm ▸ hQφ

/-- If quantifier-free types determine a formula, compactness gives a
quantifier-free formula equivalent to it in all models of the theory. -/
theorem exists_qf_equivalent (T : SortedTheory L E) (φ : SortedFormula L E Var)
    (hdet : ∀ P Q : T.PointedModel Var,
      (∀ ψ : SortedFormula L E Var, ψ.IsQF → (P.realizes ψ ↔ Q.realizes ψ)) →
      (P.realizes φ ↔ Q.realizes φ)) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : T.PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  classical
  let Good := sufficientQF (T := T) φ
  have h : ¬T.Realizable ({φ} ∪ SortedFormula.neg '' Good) := by
    rw [T.realizable_iff_pointedModel]
    rintro ⟨P, hP⟩
    obtain ⟨ψ, hψ, hPψ⟩ := exists_sufficientQF P (hP φ (Or.inl rfl)) hdet
    exact (hP ψ.neg (Or.inr ⟨ψ, hψ, rfl⟩)) hPψ
  obtain ⟨U, hU, hUnreal⟩ := T.finite_unrealizable h
  let V := U.erase φ
  have hV : (V : Set (SortedFormula L E Var)) ⊆ SortedFormula.neg '' Good := by
    intro χ hχ
    obtain ⟨hne, hχU⟩ := Finset.mem_erase.mp hχ
    exact (hU hχU).resolve_left hne
  obtain ⟨W, hW, hVW⟩ := Finset.subset_set_image_iff.mp hV
  refine ⟨SortedFormula.anyOf W.toList,
    SortedFormula.anyOf_isQF _ (fun ψ hψ => (hW (Finset.mem_toList.mp hψ)).1), ?_⟩
  intro P
  change P.realizes φ ↔ (SortedFormula.anyOf W.toList).realize P.model P.point
  rw [SortedFormula.realize_anyOf]
  constructor
  · intro hP
    by_contra! hnone
    apply hUnreal
    apply (T.realizable_iff_pointedModel).mpr
    refine ⟨P, fun χ hχ => ?_⟩
    by_cases heq : χ = φ
    · exact heq.symm ▸ hP
    · have hneg : χ ∈ W.image SortedFormula.neg :=
        hVW ▸ Finset.mem_erase.mpr ⟨heq, hχ⟩
      obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hneg
      exact hnone ψ (Finset.mem_toList.mpr hψ)
  · rintro ⟨ψ, hψ, hPψ⟩
    exact (hW (Finset.mem_toList.mp hψ)).2 P hPψ

@[expose]
def PointedModel.extend (P : T.PointedModel Var) (s : TCsort) (x : P.carrier s) :
    T.PointedModel (AddSortedVar Var s) :=
  ⟨P.carrier, P.model, extendSortedAssignment P.point x, P.nonempty, P.models⟩

theorem PointedModel.realizes_all (P : T.PointedModel Var) (s : TCsort)
    (φ : SortedFormula L E (AddSortedVar Var s)) :
    P.realizes (.all s φ) ↔ ∀ x : P.carrier s, (P.extend s x).realizes φ :=
  Iff.rfl

/-- It suffices to check invariance of quantified quantifier-free formulas
under agreement on the quantifier-free type. -/
theorem exists_qf_equivalent_of_universal (T : SortedTheory L E)
    (hdet : ∀ {Var : TCsort → Type a} (s : TCsort)
      (ψ : SortedFormula L E (AddSortedVar Var s)), ψ.IsQF → ∀ P Q : T.PointedModel Var,
      (∀ θ : SortedFormula L E Var, θ.IsQF → (P.realizes θ ↔ Q.realizes θ)) →
      (P.realizes (.all s ψ) ↔ Q.realizes (.all s ψ)))
    (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : T.PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  induction φ with
  | falsum => exact ⟨_, .falsum, fun _ => Iff.rfl⟩
  | equal t t' => exact ⟨_, .equal t t', fun _ => Iff.rfl⟩
  | rel r ts => exact ⟨_, .rel r ts, fun _ => Iff.rfl⟩
  | imp φ ψ hφ hψ =>
    obtain ⟨φ', hφq, hφe⟩ := hφ
    obtain ⟨ψ', hψq, hψe⟩ := hψ
    refine ⟨.imp φ' ψ', .imp hφq hψq, fun P => ?_⟩
    exact (hφe P).imp (hψe P)
  | all s φ ih =>
    obtain ⟨ψ, hψq, hψe⟩ := ih
    obtain ⟨χ, hχq, hχe⟩ := T.exists_qf_equivalent (.all s ψ) (hdet s ψ hψq)
    refine ⟨χ, hχq, fun P => ?_⟩
    rw [← hχe P, P.realizes_all, P.realizes_all]
    exact forall_congr' (fun x => hψe (P.extend s x))

/-- A one-point extension may be realized in any model with the same
pointed theory as the target. This is the compactness form of the
Shoenfield test, so the target need not itself be saturated. -/
theorem exists_qf_equivalent_of_onePoint (T : SortedTheory L E)
    (hstep : ∀ {Var : TCsort → Type a} (P Q : T.PointedModel Var),
      (∀ θ : SortedFormula L E Var, θ.IsQF → (P.realizes θ ↔ Q.realizes θ)) →
      ∀ (s : TCsort) (x : P.carrier s),
        ∃ (R : T.PointedModel Var) (y : R.carrier s),
          (∀ θ, Q.realizes θ ↔ R.realizes θ) ∧
          ∀ ψ : SortedFormula L E (AddSortedVar Var s), ψ.IsQF →
            ((P.extend s x).realizes ψ ↔ (R.extend s y).realizes ψ))
    (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : T.PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  apply T.exists_qf_equivalent_of_universal _ φ
  intro Var s ψ hψ P Q hPQ
  have transfer (P Q : T.PointedModel Var)
      (hPQ : ∀ θ : SortedFormula L E Var, θ.IsQF → (P.realizes θ ↔ Q.realizes θ))
      (hq : Q.realizes (.all s ψ)) : P.realizes (.all s ψ) := by
    rw [P.realizes_all]
    intro x
    obtain ⟨R, y, hQR, hxy⟩ := hstep P Q hPQ s x
    exact (hxy ψ hψ).mpr ((R.realizes_all s ψ).mp ((hQR _).mp hq) y)
  exact ⟨transfer Q P (fun θ hθ => (hPQ θ hθ).symm), transfer P Q hPQ⟩

/-- The substructure form of the Shoenfield test. The field-specific
argument supplies the extension of a generated embedding to the
enlarged tuple in a target with the same pointed theory. -/
theorem exists_qf_equivalent_of_generated_extension (T : SortedTheory L E)
    (hstep : ∀ {Var : TCsort → Type a} (P Q : T.PointedModel Var)
      (e : SortedEmbedding (P.model.termGenerated P.point).structureOn Q.model),
      (∀ s i, e.toEmbedding s (P.model.termGeneratedAssignment P.point s i) = Q.point s i) →
      ∀ (s : TCsort) (x : P.carrier s),
        ∃ (R : T.PointedModel Var) (y : R.carrier s)
          (j : SortedEmbedding
            (P.model.termGenerated (extendSortedAssignment P.point x)).structureOn R.model),
          (∀ θ, Q.realizes θ ↔ R.realizes θ) ∧
          ∀ t i, j.toEmbedding t
            (P.model.termGeneratedAssignment (extendSortedAssignment P.point x) t i) =
              extendSortedAssignment R.point y t i)
    (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : T.PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  apply T.exists_qf_equivalent_of_onePoint _ φ
  intro Var P Q hPQ s x
  obtain ⟨e, he⟩ := exists_embedding_of_same_qf_type P.model P.point Q.point hPQ
  obtain ⟨R, y, j, hR, hj⟩ := hstep P Q e he s x
  exact ⟨R, y, hR, fun ψ hψ => same_qf_type_of_generatedEmbedding P.model
    (extendSortedAssignment P.point x) (extendSortedAssignment R.point y) j hj ψ hψ⟩

/-- Partial elementarity of the generated embeddings is also enough
for the Shoenfield test. -/
theorem exists_qf_equivalent_of_generated_partial_elementarity (T : SortedTheory L E)
    (h : ∀ {Var : TCsort → Type a} (P Q : T.PointedModel Var)
      (e : SortedEmbedding (P.model.termGenerated P.point).structureOn Q.model),
      (∀ s i, e.toEmbedding s (P.model.termGeneratedAssignment P.point s i) = Q.point s i) →
      ∀ φ : SortedFormula L E Var, P.realizes φ ↔ Q.realizes φ)
    (φ : SortedFormula L E Var) :
    ∃ ψ : SortedFormula L E Var, ψ.IsQF ∧
      ∀ P : T.PointedModel Var, P.realizes φ ↔ P.realizes ψ := by
  apply T.exists_qf_equivalent φ
  intro P Q hPQ
  obtain ⟨e, he⟩ := exists_embedding_of_same_qf_type P.model P.point Q.point hPQ
  exact h P Q e he φ

end SortedTheory

end GeneralizedEuler.Section2
