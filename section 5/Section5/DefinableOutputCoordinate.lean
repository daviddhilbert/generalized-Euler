module

public import Section5.DefinableRelations
public import Section5.DefinableBijectionSchemes
public import Section5.UnaryFactorizationStep

/-! The first relatively unary factor projects the old graph while
retaining the complementary input field coordinates. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type} [Finite J]

@[expose] def recordOutputAssignment (i j : Fin n)
    (a : SortedAssignment X (MixedVariables n I)) (b : SortedAssignment X (MixedVariables n J)) :
    SortedAssignment X (MixedVariables n J)
  | .vf => Function.update (a .vf) i (b .vf j)
  | .rv => b .rv

theorem recordOutputAssignment_graph (i j : Fin n)
    (R : SortedAssignment X (MixedVariables n I) → SortedAssignment X (MixedVariables n J) → Prop)
    (hR : DefinableRelation M S.carrier R) :
    DefinableRelation M S.carrier (fun a b => ∃ y, R a y ∧ recordOutputAssignment i j a y = b) := by
  let U := MixedVariables n I
  let V := MixedVariables n J
  let W := SumVariables (SumVariables U V) V
  let rename (s : TCsort) : SumVariables U V s → W s := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have head := SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W)
    .vf (.inl (.inr i)) (.inr j)
  have tail := SortedDefinableOver.iInter (fun k : {k : Fin n // k ≠ i} =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W)
      .vf (.inl (.inr k.val)) (.inl (.inl k.val)))
  have tags := SortedDefinableOver.iInter (fun k : J =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W)
      .rv (.inl (.inr k)) (.inr k))
  unfold DefinableRelation at hR ⊢
  have all := (hR.pullback_relabel rename).inter (head.inter (tail.inter tags))
  convert definable_project_mixed all using 1
  ext w
  let a : SortedAssignment X U := fun s => w s ∘ Sum.inl
  let b : SortedAssignment X V := fun s => w s ∘ Sum.inr
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  change (∃ y : SortedAssignment X V, R a y ∧ recordOutputAssignment i j a y = b) ↔
    ∃ y : SortedAssignment X V, R a y ∧ b .vf i = y .vf j ∧
      (∀ k : {k : Fin n // k ≠ i}, b .vf k.val = a .vf k.val) ∧ (∀ k, b .rv k = y .rv k)
  constructor
  · rintro ⟨y,h,eq⟩
    rw [← eq]
    exact ⟨y,h,Function.update_self i _ _,fun k => Function.update_of_ne k.property _ _,fun _ => rfl⟩
  · rintro ⟨y,h,hi,hk,hr⟩
    refine ⟨y,h,?_⟩
    funext s k
    cases s
    · change Function.update (a .vf) i (y .vf j) k = b .vf k
      by_cases eq : k = i
      · subst k
        rw [Function.update_self,hi]
      · rw [Function.update_of_ne eq, hk ⟨k,eq⟩]
    · exact (hr k).symm

end GeneralizedEuler.Section5
