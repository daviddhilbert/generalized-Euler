module

public import Section5.RelativeRVObjectSchemes
public import Section5.RelativeTaggedIsoNaming
public import Section5.PositiveRVClasses
public import Section5.GluedTaggedIsomorphisms

/-! Finite families of named RV objects have classes over the generated
base and classes glued over a fixed selection of the parameter indices. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}
  {I J : Type} [Fintype I] [Fintype J]

abbrev RelativeObjectFamily (M : SortedStructure L E X) (S : SortedSubstructure M) (P : TCsort → Type) (I : Type) :=
  I → RelativeRVObjectScheme M S P

namespace RelativeObjectFamily

variable (A : RelativeObjectFamily M S P I) (B : RelativeObjectFamily M S P J)
  (zero : S.carrier .rv) (hz : zero.val = M.funMap .rvZero (fun j => j.elim0))

abbrev Valid (p : SortedAssignment X P) := ∀ i, (A i).valid zero p

abbrev IsoScheme (A : RelativeObjectFamily M S P I) (B : RelativeObjectFamily M S P J) :=
  RelativeTaggedIsoScheme (fun i => (A i).data) (fun j => (B j).data)

theorem valid_definable : SortedDefinableOver M S.carrier {p | Valid A zero p} := by
  convert SortedDefinableOver.iInter (fun i => (A i).valid_definable zero) using 1
  ext p
  exact (Set.mem_iInter (x := p) (s := fun i => {p | (A i).valid zero p})).symm

@[expose] def fiberClass (p : SortedAssignment X P) (v : Valid A zero p) :
    RVSemiring M (M.termGenerated (namedTuple S p)) :=
  ∑ i, objectClass M _ ⟨(A i).data.degree,(A i).realize zero hz p (v i)⟩

theorem isoScheme_of_fiberClass_eq (p : SortedAssignment X P)
    (vA : Valid A zero p) (vB : Valid B zero p)
    (eq : fiberClass A zero hz p vA = fiberClass B zero hz p vB) :
    ∃ W : IsoScheme A B, W.valid p := by
  apply relative_tagged_iso_scheme_of_class_eq p
    (fun i => (A i).data) (fun j => (B j).data)
    (fun i => (A i).realize zero hz p (vA i)) (fun j => (B j).realize zero hz p (vB j))
    (fun _ => rfl) (fun _ => rfl) _ _ eq
  all_goals
    intro i u
    have same : rvTupleAssignment (u .rv) = u := by
      funext s j
      cases s
      · exact j.elim
      · rfl
    exact (congrArg (fun v => appendAssignments p v ∈ _) same).symm.to_iff

theorem positive_class_has_named_family (p : SortedAssignment X P)
    (sat : ∀ d, let T := M.termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes M (WithBase T.carrier (RVVariables (Fin d)))
        (BaseAssignments T.carrier (RVVariables (Fin d))))
    (a : RVSemiring M (M.termGenerated (namedTuple S p))) :
    ∃ (n : ℕ) (W : RelativeObjectFamily M S P (Fin n)) (v : Valid W zero p),
      fiberClass W zero hz p v = a := by
  obtain ⟨n,U,eq⟩ := positive_class_represented M (M.termGenerated (namedTuple S p)) a
  choose W valid matchClass using fun i =>
    relative_rv_object_scheme_of_actual p zero hz (U i).2 (sat (U i).1)
  refine ⟨n,W,valid,?_⟩
  rw [fiberClass,eq]
  exact Finset.sum_congr rfl (fun i _ => matchClass i)

variable {h t : ℕ} (D : RelativeRVIndex M S h t)
  (C : RelativeObjectFamily M S (RVVariables (Fin h)) I)

@[expose] def gluedClass (v : ∀ p ∈ D.labels, Valid C zero (rvTupleAssignment p)) : RVSemiring M S :=
  ∑ i, ((C i).row zero hz D (fun p hp => v p hp i)).gluedClass

theorem gluedClass_eq_of_isoScheme
    {F : RelativeObjectFamily M S (RVVariables (Fin h)) J}
    (vC : ∀ p ∈ D.labels, Valid C zero (rvTupleAssignment p))
    (vF : ∀ p ∈ D.labels, Valid F zero (rvTupleAssignment p))
    (w : IsoScheme C F) (valid : ∀ p ∈ D.labels, w.valid (rvTupleAssignment p)) :
    gluedClass zero hz D C vC = gluedClass zero hz D F vF :=
  w.gluedClass_sum_eq (fun i => (C i).row zero hz D (fun p hp => vC p hp i))
    (fun j => (F j).row zero hz D (fun p hp => vF p hp j)) valid

end RelativeObjectFamily

end GeneralizedEuler.Section5
