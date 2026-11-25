module

public import Section2.RecoveredValuedField
public import Section3.DefinablePartitions

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set
variable {L : Language} {E : Type*} {V : TCsort → Type*}

/-- A term in the named field inputs and field-base parameters. The
valuation-ring predicate adds no function symbols. -/
def fieldTermAt {I : Type*} (fieldNames : I → V .vf) (t : (convexLanguage L).Term I) :
    SortedTerm L E V .vf := liftValuedTerm (fun i => .var (fieldNames i)) t

/-- Over all pointed models of the fixed-base theory, membership of the
output in the field closure of the inputs gives one finite list of pure
field terms. The bound is uniform over every auxiliary input (3.3).
The output variable is separate from the fieldNames tuple. -/
theorem finite_field_terms_of_output_closure {I : Type*} (T : SortedTheory L E)
    (graph : SortedFormula L E V) (fieldNames : I → V .vf) (output : V .vf)
    (hclosure : ∀ P : T.PointedModel V, P.realizes graph →
      letI := valuedStructureOfSorted P.model ∅
      P.point .vf output ∈ Substructure.closure (convexLanguage L) (range (P.point .vf ∘ fieldNames))) :
    ∃ terms : Finset ((convexLanguage L).Term I), ∀ P : T.PointedModel V, P.realizes graph →
      ∃ t ∈ terms, (fieldTermAt fieldNames t).realize P.model P.point = P.point .vf output := by
  classical
  let test (t : (convexLanguage L).Term I) : SortedFormula L E V :=
    .equal (fieldTermAt fieldNames t) (.var output)
  apply T.exists_finite_formula_cover graph test
  intro P hg
  let := valuedStructureOfSorted P.model ∅
  let params := P.point .vf ∘ fieldNames
  obtain ⟨t,ht⟩ := Substructure.mem_closure_iff_exists_term.mp (hclosure P hg)
  let pick (x : range params) := x.property.choose
  have hnames : params ∘ pick = Subtype.val := funext fun x => x.property.choose_spec
  refine ⟨t.relabel pick,?_⟩
  change (liftValuedTerm (fun i => SortedTerm.var (fieldNames i)) (t.relabel pick)).realize
    P.model P.point = P.point .vf output
  rw [realize_liftValuedTerm P.model (∅ : Set (P.carrier .vf))]
  change (t.relabel pick).realize params = _
  rwa [Term.realize_relabel,hnames]

/-- Cover a whole atomic branch by terms and select a single term on it
(3.34 and 3.36). It suffices that the agreement loci use the named base. -/
theorem single_field_branch_of_atomic_cover {X K I : Type*} {D : Set (Set X)} {A : Set X}
    (hA : GeneratesType D A) (f : X → K) (pieces : I → X → K)
    (defeq : ∀ i, {x | pieces i x = f x} ∈ D)
    (cov : ∀ x ∈ A, ∃ i, pieces i x = f x) : ∃ i, EqOn (pieces i) f A := by
  obtain ⟨x,hx⟩ := hA.nonempty
  obtain ⟨i,hi⟩ := cov x hx
  exact ⟨i,fun y hy => (hA.uniform _ (defeq i) x hx y hy).mp hi⟩

end GeneralizedEuler.Section3
