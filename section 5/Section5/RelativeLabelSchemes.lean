module

public import Section5.UniformRelativeRVLifts
public import Section5.InjectiveObjectLifts

/-! Name an actual RV object's tags and structure map by formulas over
the original base and a free parameter tuple. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}
  {k : ℕ} (p : SortedAssignment X P)

@[expose] def RVObject.LabelRelation {T : SortedSubstructure M} (B : RVObject M T k)
    (a : SortedAssignment X (RVVariables (Fin B.arity))) (b : SortedAssignment X (RVVariables (Fin k))) : Prop :=
  ∃ h : a .rv ∈ B.carrier, B.label ⟨a .rv,h⟩ = b .rv

theorem RVObject.labelRelation_definable {T : SortedSubstructure M} (B : RVObject M T k) :
    DefinableRelation M T.carrier (RVObject.LabelRelation B) := by
  apply (ObjectLift.relation_of_rvGraph B.graph).congr
  intro a b
  constructor
  · rintro ⟨u,v,h⟩
    have mem : a .rv ∈ B.carrier := v ▸ u.property
    exact ⟨mem,(congrArg B.label (Subtype.ext v.symm)).trans h⟩
  · rintro ⟨mem,h⟩
    exact ⟨⟨_,mem⟩,rfl,h⟩

theorem relative_rv_labels_of_object (B : RVObject M (M.termGenerated (namedTuple S p)) k) :
    let U := RVVariables (Fin B.arity)
    let V := RVVariables (Fin k)
    ∃ (D : Set (SortedAssignment X (SumVariables P U)))
      (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))),
      SortedDefinableOver M S.carrier D ∧ SortedDefinableOver M S.carrier G ∧
      (∀ a : SortedAssignment X U, appendAssignments p a ∈ D ↔ a .rv ∈ B.carrier) ∧
      ∀ a b, appendAssignments (appendAssignments p a) b ∈ G ↔ RVObject.LabelRelation B a b := by
  obtain ⟨D,defD,hD⟩ := definable_fiber_as_scheme p _ B.definable
  obtain ⟨G,defG,hG⟩ := definable_relation_fiber_as_scheme p _ (RVObject.labelRelation_definable B)
  exact ⟨D,G,defD,defG,hD,hG⟩

theorem relativeRVWitness_of_labelRelation
    (B : RVObject M (M.termGenerated (namedTuple S p)) k)
    {D : Set (SortedAssignment X (SumVariables P (RVVariables (Fin B.arity))))}
    {G : Set (SortedAssignment X
      (SumVariables (SumVariables P (RVVariables (Fin B.arity))) (RVVariables (Fin k))))}
    (matchD : ∀ a, appendAssignments p a ∈ D ↔ a .rv ∈ B.carrier)
    (matchG : ∀ a b, appendAssignments (appendAssignments p a) b ∈ G ↔ RVObject.LabelRelation B a b)
    (zero : X .rv) (sameZero : zero = M.funMap .rvZero (fun i => i.elim0))
    (bound : ℕ) (fibers : ∀ (x : Fin k → X .rv) (a : Fin (bound+1) → B.carrier),
      (∀ i, B.label (a i) = x) → ¬ Function.Injective a) :
    RelativeRVWitness D G zero bound p := by
  simp only [RelativeRVWitness,matchD,matchG,RVObject.LabelRelation]
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    exact ⟨fun ha => ⟨rvTupleAssignment (B.label ⟨a .rv,ha⟩),ha,rfl⟩,fun ⟨_,ha,_⟩ => ha⟩
  · rintro a v w ⟨ha,hv⟩ ⟨_,hw⟩
    funext s j
    cases s
    · exact j.elim
    · exact congrFun (hv.symm.trans hw) j
  · rintro a v ⟨ha,hv⟩ j
    rw [← hv,sameZero]
    exact B.nonzero ⟨a .rv,ha⟩ j
  · intro v a h inj
    let f (j : Fin (bound+1)) : B.carrier := ⟨(a j) .rv,(h j).choose⟩
    apply fibers (v .rv) f (fun j => (h j).choose_spec)
    intro j j' eq
    apply inj
    funext s l
    cases s
    · exact l.elim
    · exact congrFun (congrArg Subtype.val eq) l

end GeneralizedEuler.Section5
