module

public import Section5.NamedFieldFunctions

/-! Totalize a single-valued field relation over any mixed parameter
tuple by using a named value outside its domain. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P : TCsort → Type}

theorem definable_partial_field_function
    (R : SortedAssignment X P → fieldAssignment 1 X → Prop)
    (graph : DefinableRelation M S.carrier R)
    (unique : ∀ a b c, R a b → R a c → b = c)
    (default : S.carrier .vf) :
    ∃ f : SortedAssignment X P → X .vf,
      (∀ a b, R a b → f a = b .vf 0) ∧
      DefinableRelation M S.carrier (fun a (b : fieldAssignment 1 X) => f a = b .vf 0) := by
  classical
  let p (a : SortedAssignment X P) := ∃ b, R a b
  let f (a : SortedAssignment X P) := if h : p a then h.choose .vf 0 else default.val
  have eval (a : SortedAssignment X P) (b : fieldAssignment 1 X) (h : R a b) : f a = b .vf 0 := by
    have yes : p a := ⟨b,h⟩
    unfold f
    rw [dite_eq_left yes,unique a _ b yes.choose_spec h]
  refine ⟨f,eval,?_⟩
  let U := MixedVariables 1 Empty
  let V := SumVariables P U
  let term : SortedTerm L E (WithBase S.carrier V) .vf := .var (.inl default)
  have const : DefinableRelation M S.carrier (fun (_ : SortedAssignment X P) (b : fieldAssignment 1 X) =>
      default.val = b .vf 0) := by
    unfold DefinableRelation
    convert SortedDefinableOver.coordinate_eq_term (M := M) (A := S.carrier) (Var := V) .vf (.inr 0) term using 1
    ext a
    exact eq_comm
  have all : SortedDefinableOver M S.carrier (Set.univ : Set (fieldAssignment 1 X)) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  have domain : SortedDefinableOver M S.carrier {a | p a} := by
    convert graph.preimage all using 1
    ext a
    exact ⟨fun ⟨b,hb⟩ => ⟨b,Set.mem_univ _,hb⟩,fun ⟨b,_,hb⟩ => ⟨b,hb⟩⟩
  apply (graph.union (const.inter_left domain.compl)).congr
  intro a b
  constructor
  · rintro (h | ⟨h,hn⟩)
    · exact eval a b h
    · simpa only [f,dite_eq_right (show ¬ p a from hn)] using h
  · intro e
    by_cases yes : p a
    · apply Or.inl
      have eq : yes.choose = b := fieldAssignment_ext (fun i => by
        rw [Subsingleton.elim i (0 : Fin 1)]
        simpa only [f,dite_eq_left yes] using e)
      exact eq ▸ yes.choose_spec
    · exact Or.inr ⟨by simpa only [f,dite_eq_right yes] using e,yes⟩

end GeneralizedEuler.Section5
