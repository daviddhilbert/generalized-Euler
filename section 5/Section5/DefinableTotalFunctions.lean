module

public import Section5.DefinableRelations

/-! Complete a single-valued definable relation with one fixed
definable output on its complement. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P V : TCsort → Type} [Finite (V .vf)] [Finite (V .rv)]

theorem definable_total_function
    (R : SortedAssignment X P → SortedAssignment X V → Prop)
    (graph : DefinableRelation M S.carrier R)
    (unique : ∀ a b c, R a b → R a c → b = c)
    (z : SortedAssignment X V)
    (defZ : DefinableRelation M S.carrier (fun (_ : SortedAssignment X P) b => z = b)) :
    ∃ f : SortedAssignment X P → SortedAssignment X V,
      (∀ a b, R a b → f a = b) ∧ DefinableRelation M S.carrier (fun a b => f a = b) := by
  classical
  let p (a : SortedAssignment X P) := ∃ b, R a b
  let f (a : SortedAssignment X P) := if h : p a then h.choose else z
  have eval (a : SortedAssignment X P) (b : SortedAssignment X V) (h : R a b) : f a = b := by
    have yes : p a := ⟨b,h⟩
    unfold f
    rw [dite_eq_left yes,unique a _ b yes.choose_spec h]
  refine ⟨f,eval,?_⟩
  have all : SortedDefinableOver M S.carrier (Set.univ : Set (SortedAssignment X V)) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  have domain : SortedDefinableOver M S.carrier {a | p a} := by
    convert graph.preimage all using 1
    ext a
    exact ⟨fun ⟨b,hb⟩ => ⟨b,Set.mem_univ _,hb⟩,fun ⟨b,_,hb⟩ => ⟨b,hb⟩⟩
  apply (graph.union (defZ.inter_left domain.compl)).congr
  intro a b
  constructor
  · rintro (h | ⟨h,hn⟩)
    · exact eval a b h
    · simpa only [f,dite_eq_right (show ¬ p a from hn)] using h
  · intro e
    by_cases yes : p a
    · exact Or.inl ((show yes.choose = b by simpa only [f,dite_eq_left yes] using e) ▸ yes.choose_spec)
    · exact Or.inr ⟨by simpa only [f,dite_eq_right yes] using e,yes⟩

end GeneralizedEuler.Section5
