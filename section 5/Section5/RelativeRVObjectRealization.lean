module

public import Section5.UniformGradedLiftPresentations

/-! A valid relative RV graph defines an actual RV object over the
generated base of its parameters. Its lift is the corresponding
fiber of the relative lift set. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type} {m k : ℕ}

local notation "U" => RVVariables (Fin m)
local notation "V" => RVVariables (Fin k)

private theorem rvTupleAssignment_eta {n : ℕ} (a : SortedAssignment X (RVVariables (Fin n))) :
    rvTupleAssignment (a .rv) = a := by
  funext s i
  cases s
  · exact i.elim
  · rfl

variable (p : SortedAssignment X P)
  {D : Set (SortedAssignment X (SumVariables P (RVVariables (Fin m))))}
  {G : Set (SortedAssignment X (SumVariables (SumVariables P (RVVariables (Fin m))) (RVVariables (Fin k))))}
  (defD : SortedDefinableOver M S.carrier D) (defG : SortedDefinableOver M S.carrier G)
  {bound : ℕ}


@[expose] def relativeTagSet (D : Set (SortedAssignment X (SumVariables P U))) : Set (Fin m → X .rv) :=
  {t | appendAssignments p (rvTupleAssignment t) ∈ D}


include defD in
theorem realized_relative_tag_definable : isRVSet M (M.termGenerated (namedTuple S p)) (relativeTagSet p D) := by
  have h := definable_scheme_at_fiber p D defD
  unfold isRVSet
  convert h using 1
  ext a
  change appendAssignments p (rvTupleAssignment (a .rv)) ∈ D ↔ appendAssignments p a ∈ D
  rw [rvTupleAssignment_eta]

variable (h : RelativeRVWitness D G (M.funMap .rvZero (fun i => i.elim0)) bound p)

include h in
@[expose] def relativeTagLabel (x : relativeTagSet p D) : Fin k → X .rv :=
  (((h.1 (rvTupleAssignment x.val)).1 x.property).choose) .rv

theorem relativeTagLabel_in_graph (a : relativeTagSet p D) :
    appendAssignments (appendAssignments p (rvTupleAssignment a.val))
      (rvTupleAssignment (relativeTagLabel p h a)) ∈ G := by
  unfold relativeTagLabel
  rw [rvTupleAssignment_eta]
  exact ((h.1 (rvTupleAssignment a.val)).1 a.property).choose_spec

private theorem relativeTagLabel_test (a : relativeTagSet p D) (u : Fin k → X .rv) :
    relativeTagLabel p h a = u ↔
      appendAssignments (appendAssignments p (rvTupleAssignment a.val)) (rvTupleAssignment u) ∈ G := by
  constructor
  · intro eq
    rw [← eq]
    exact relativeTagLabel_in_graph p h a
  · intro mem
    exact congrFun (h.2.1 (rvTupleAssignment a.val) _ _ (relativeTagLabel_in_graph p h a) mem) .rv

include defG in
theorem relativeTagLabel_definable : SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier (rvGraph (relativeTagLabel p h)) := by
  let T := RVVariables (Fin m ⊕ Fin k)
  let new : (s : TCsort) → SumVariables U V s → T s
    | .vf => Sum.elim PEmpty.elim PEmpty.elim
    | .rv => id
  let assoc (s : TCsort) : SumVariables (SumVariables P U) V s → SumVariables P (SumVariables U V) s :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  have named := definable_scheme_at_fiber p _ (defG.pullback_relabel assoc)
  convert named.pullback_relabel new using 1
  ext x
  let t := x .rv ∘ Sum.inl
  let u := x .rv ∘ Sum.inr
  have out : (fun s => appendAssignments p (fun s => x s ∘ new s) s ∘ assoc s) =
      appendAssignments (appendAssignments p (rvTupleAssignment t)) (rvTupleAssignment u) := by
    funext s i
    rcases i with (i | i) | i
    · rfl
    · cases s
      · exact i.elim
      · rfl
    · cases s
      · exact i.elim
      · rfl
  change (∃ a : relativeTagSet p D, a.val = t ∧ relativeTagLabel p h a = u) ↔
    (fun s => appendAssignments p (fun s => x s ∘ new s) s ∘ assoc s) ∈ G
  rw [out]
  constructor
  · rintro ⟨a,ha,eq⟩
    have mem := (relativeTagLabel_test p h a u).1 eq
    rwa [ha] at mem
  · intro mem
    have ht : appendAssignments p (rvTupleAssignment t) ∈ D := (h.1 _).2 ⟨rvTupleAssignment u,mem⟩
    exact ⟨⟨t,ht⟩,rfl,(relativeTagLabel_test p h ⟨t,ht⟩ u).2 mem⟩

include defD defG h in
@[expose] def realizedRelativeRVObject : RVObject M (M.termGenerated (namedTuple S p)) k where
  arity := m
  carrier := relativeTagSet p D
  definable := realized_relative_tag_definable p defD
  label := relativeTagLabel p h
  graph := relativeTagLabel_definable p defG h
  nonzero a := h.2.2.1 (rvTupleAssignment a.val) (rvTupleAssignment (relativeTagLabel p h a))
    (relativeTagLabel_in_graph p h a)
  finiteFibers u := by
    have fin := h.finite_fiber (rvTupleAssignment u)
    let f (x : relativeTagSet p D) := rvTupleAssignment x.val
    have inj : Function.Injective f := fun _ _ e => Subtype.ext (congrFun e .rv)
    apply (fin.preimage inj.injOn).subset
    intro a eq
    exact (relativeTagLabel_test p h a u).1 eq

theorem realizedRelativeRVObject_lift_eq :
    {x : SortedAssignment X (MixedVariables k (Fin m)) | appendAssignments p x ∈ relativeRVLift (M := M) G} =
      ObjectLift.carrier (realizedRelativeRVObject p defD defG h) := by
  ext x
  let u := M.rvMap ∘ x .vf
  let t := x .rv
  change appendAssignments (appendAssignments p (rvTupleAssignment t)) (rvTupleAssignment u) ∈ G ↔
    ∃ a : relativeTagSet p D, a.val = t ∧ relativeTagLabel p h a = u
  constructor
  · intro mem
    have ht : t ∈ relativeTagSet p D := (h.1 _).2 ⟨rvTupleAssignment u,mem⟩
    exact ⟨⟨t,ht⟩,rfl,(relativeTagLabel_test p h ⟨t,ht⟩ u).2 mem⟩
  · rintro ⟨a,ha,eq⟩
    have mem := (relativeTagLabel_test p h a u).1 eq
    rwa [ha] at mem

theorem RelativeRVLiftScheme.has_actual_lift {W : TCsort → Type}
    (i : RelativeRVLiftScheme M S P W)
    (A : Set (SortedAssignment X (SumVariables P W)))
    (zero : S.carrier .rv) (hzero : zero.val = M.funMap .rvZero (fun j => j.elim0))
    (valid : i.valid A zero p) :
    ∃ B : RVObject M (M.termGenerated (namedTuple S p)) i.degree,
      B.arity = i.arity ∧ MixedDefinablyEquivalent M (M.termGenerated (namedTuple S p))
        {u | appendAssignments p u ∈ A} (ObjectLift.carrier B) := by
  have h : RelativeRVWitness i.tags i.labelGraph (M.funMap .rvZero (fun j => j.elim0)) i.bound p := hzero ▸ valid.1
  let B := realizedRelativeRVObject p i.tagsDefinable i.labelDefinable h
  have eq := realizedRelativeRVObject_lift_eq p i.tagsDefinable i.labelDefinable h
  let f := valid.2.equiv.trans (Set.equivOfEq eq)
  refine ⟨B,rfl,f,?_⟩
  refine (definable_relation_scheme_at_fiber p i.liftGraph i.liftGraphDefinable).congr ?_
  intro a b
  constructor
  · intro hg
    have ha := (valid.2.1 a).2 ⟨b,hg⟩
    exact ⟨ha,(valid.2.equiv_graph ⟨a,ha⟩ b).1 hg⟩
  · rintro ⟨ha,hf⟩
    exact (valid.2.equiv_graph ⟨a,ha⟩ b).2 hf

end GeneralizedEuler.Section5
