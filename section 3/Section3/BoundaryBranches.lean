module

public import Section3.FieldBranches
import all Section3.FieldBranches
public import Section3.BoundaryDimension
public import Section2.SortedQuantifierBlock

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {L : Language} {E : Type*} {V : TCsort → Type*}

private def rvOf (t : SortedTerm L E V .vf) : SortedTerm L E V .rv :=
  .app .rv (fun i => by have he : i = 0 := Fin.fin_one_eq_zero (i : Fin 1); subst i; exact t)

private theorem rvOf_realize {Z : TCsort → Type*} (M : SortedStructure L E Z)
    (v : ∀ s, V s → Z s) (t : SortedTerm L E V .vf) :
    (rvOf t).realize M v = M.rvMap (t.realize M v) := M.funMap_rv _

/-- The graph in the compactness argument of 3.26. Quantify the two
field witnesses in the same leading-term fiber, one on each side. -/
def cutFiberFormula (φ : SortedFormula L E (AddSortedVar V .vf)) (label : V .rv) :
    SortedFormula L E V :=
  let x : SortedTerm L E (AddSortedVar V .vf) .vf := .var (.inr ⟨rfl⟩)
  let u : SortedTerm L E (AddSortedVar V .vf) .rv := .var (.inl label)
  let fiber := SortedFormula.equal (rvOf x) u
  ((SortedFormula.all .vf ((fiber.conjunction φ).neg)).neg).conjunction
    ((SortedFormula.all .vf ((fiber.conjunction φ.neg).neg)).neg)

theorem cutFiberFormula_realize {Z : TCsort → Type*} (M : SortedStructure L E Z)
    (v : ∀ s, V s → Z s) (φ : SortedFormula L E (AddSortedVar V .vf)) (label : V .rv) :
    (cutFiberFormula φ label).realize M v ↔ v .rv label ∈ rvBoundary M.rvMap
      {x | φ.realize M (extendSortedAssignment v x)} := by
  simp only [cutFiberFormula,SortedFormula.realize_conjunction,SortedFormula.realize_neg,
    SortedFormula.realize,not_forall,not_not,rvOf_realize]
  change ((∃ x, M.rvMap x = v .rv label ∧ _) ∧ (∃ x, M.rvMap x = v .rv label ∧ _)) ↔
    ((∃ x, _ ∧ M.rvMap x = v .rv label) ∧ ∃ x, M.rvMap x = v .rv label ∧ _)
  exact and_congr (exists_congr (fun _ => and_comm)) Iff.rfl

/-- Boundary labels have representatives over the base enlarged by the
field inputs (3.21). Compactness converts these pointwise representatives
into finitely many *pure field terms*. The list may overcount a slice,
which suffices for the dimension estimate and avoids a choice of centers. -/
theorem finite_boundary_branches {I : Type*} (T : SortedTheory L E)
    (φ : SortedFormula L E (AddSortedVar V .vf)) (label : V .rv) (fieldNames : I → V .vf)
    (point : ∀ P : T.PointedModel V, P.realizes (cutFiberFormula φ label) →
      letI := valuedStructureOfSorted P.model ∅
      ∃ x ∈ Substructure.closure (convexLanguage L) (range (P.point .vf ∘ fieldNames)),
        P.model.rvMap x = P.point .rv label) :
    ∃ terms : Finset ((convexLanguage L).Term I), ∀ P : T.PointedModel V,
      P.realizes (cutFiberFormula φ label) → ∃ t ∈ terms,
        P.model.rvMap ((fieldTermAt fieldNames t).realize P.model P.point) = P.point .rv label := by
  classical
  let test (t : (convexLanguage L).Term I) : SortedFormula L E V :=
    .equal (rvOf (fieldTermAt fieldNames t)) (.var label)
  suffices ∃ terms : Finset _, ∀ P : T.PointedModel V, P.realizes (cutFiberFormula φ label) →
      ∃ t ∈ terms, P.realizes (test t) by
    obtain ⟨terms,h⟩ := this
    refine ⟨terms,fun P hp => ?_⟩
    obtain ⟨t,ht,he⟩ := h P hp
    exact ⟨t,ht,(rvOf_realize P.model P.point _).symm.trans he⟩
  apply T.exists_finite_formula_cover
  intro P hp
  let := valuedStructureOfSorted P.model ∅
  let names := P.point .vf ∘ fieldNames
  obtain ⟨x,hx,he⟩ := point P hp
  obtain ⟨t,ht⟩ := Substructure.mem_closure_iff_exists_term.mp hx
  let pick (x : range names) := x.property.choose
  have choose_eq : names ∘ pick = Subtype.val := funext fun x => x.property.choose_spec
  refine ⟨t.relabel pick,?_⟩
  change (rvOf (fieldTermAt fieldNames (t.relabel pick))).realize P.model P.point = _
  rw [rvOf_realize]
  apply Eq.trans _ he
  congr 1
  change (liftValuedTerm (fun i => SortedTerm.var (fieldNames i)) (t.relabel pick)).realize _ _ = _
  rw [realize_liftValuedTerm P.model (∅ : Set (P.carrier .vf))]
  change (t.relabel pick).realize names = _
  rwa [Term.realize_relabel,choose_eq]

end GeneralizedEuler.Section3
