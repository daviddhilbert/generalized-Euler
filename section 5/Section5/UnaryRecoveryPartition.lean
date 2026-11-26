module

public import Section5.DefinableOutputCoordinate
public import Section5.DefinableCovers
public import Section5.FieldTermWitnesses

/-! A finite fixed-base partition chooses the recovered output
coordinate and its term tuple before the relatively unary step. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type} [Finite J]

local notation "U" => MixedVariables n I
local notation "V" => MixedVariables n J
local notation "F" => MixedVariables n Empty

@[expose] def recoveryInput (i j : Fin n) (a : SortedAssignment X U) (b : SortedAssignment X V) :
    SortedAssignment X F
  | .vf => Function.update (a .vf) i (b .vf j)
  | .rv => Empty.elim

theorem recovery_terms_definable (i j : Fin n) (T : FieldTermTuple M S F n)
    (R : SortedAssignment X U → SortedAssignment X V → Prop) (hR : DefinableRelation M S.carrier R) :
    SortedDefinableOver M S.carrier {a | ∃ b, R a b ∧
      (realizeFieldTuple T (recoveryInput i j a b)) .vf = b .vf} := by
  let W := SumVariables U V
  let names (s : TCsort) : WithBase S.carrier F s → WithBase S.carrier W s
    | .inl c => .inl c
    | .inr k => match s with
      | .vf => .inr (if k = i then .inr j else .inl k)
      | .rv => k.elim
  have he := SortedDefinableOver.iInter (fun k : Fin n =>
    SortedDefinableOver.coordinate_eq_term (M := M) (A := S.carrier) (Var := W)
      .vf (.inr k) ((T k).relabel names))
  unfold DefinableRelation at hR
  convert definable_project_mixed (hR.inter he) using 1
  ext a
  let value (b : SortedAssignment X V) (s : TCsort) : WithBase S.carrier W s → X s :=
    Sum.elim Subtype.val (appendAssignments a b s)
  have eval (b : SortedAssignment X V) : (fun s => value b s ∘ names s) =
      (fun s => Sum.elim Subtype.val (recoveryInput i j a b s)) := by
    funext s k
    rcases k with c | k
    · cases s <;> rfl
    · cases s
      · by_cases h : k = i
        · subst k
          simp [names,value,appendAssignments,recoveryInput]
        · simp [names,value,appendAssignments,recoveryInput,h]
      · exact k.elim
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  change (∃ b, R a b ∧ (realizeFieldTuple T (recoveryInput i j a b)) .vf = b .vf) ↔
    ∃ b, R a b ∧ ∀ k, b .vf k = ((T k).relabel names).realize M (value b)
  simp only [SortedTerm.realize_relabel,eval]
  exact exists_congr fun b => and_congr_right fun _ =>
    ⟨fun h k => (congrFun h k).symm,fun h => funext fun k => (h k).symm⟩

theorem finite_recovered_output_partition
    (i : Fin n) (A : Set (SortedAssignment X U)) (B : Set (SortedAssignment X V)) (f : A ≃ B)
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier U) (BaseAssignments S.carrier U))
    (ha : SortedDefinableOver M S.carrier A)
    (hf : DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ A, (f ⟨a,h⟩).val = b))
    (recover : ∀ a : A, ∃ (j : Fin n) (T : FieldTermTuple M S F n),
      (realizeFieldTuple T (recoveryInput i j a.val (f a).val)) .vf = (f a).val .vf) :
    ∃ (C : Finset (Fin n × FieldTermTuple M S F n)) (pieces : {q // q ∈ C} → Set (SortedAssignment X U)),
      (∀ q, SortedDefinableOver M S.carrier (pieces q)) ∧ (∀ q, pieces q ⊆ A) ∧
      Pairwise (fun q q' => Disjoint (pieces q) (pieces q')) ∧ (⋃ q, pieces q) = A ∧
      ∀ q (x y : A), x.val ∈ pieces q → y.val ∈ pieces q →
        (∀ k, k ≠ i → x.val .vf k = y.val .vf k) →
        (f x).val .vf q.val.1 = (f y).val .vf q.val.1 → (f x).val .vf = (f y).val .vf := by
  let Test := Fin n × FieldTermTuple M S F n
  let D (q : Test) := {a | ∃ b, (∃ h : a ∈ A, (f ⟨a,h⟩).val = b) ∧
    (realizeFieldTuple q.2 (recoveryInput i q.1 a b)) .vf = b .vf}
  have hd (q : Test) : SortedDefinableOver M S.carrier (D q) := recovery_terms_definable i q.1 q.2 _ hf
  obtain ⟨C,pieces,hp,sub,disj,cover⟩ := finite_definable_partition_of_cover sat A ha D hd (by
    intro a h
    obtain ⟨j,T,eq⟩ := recover ⟨a,h⟩
    exact ⟨(j,T),_,⟨h,rfl⟩,eq⟩)
  refine ⟨C,pieces,hp,fun q a h => ?_,disj,cover,?_⟩
  · obtain ⟨_,⟨hA,_⟩,_⟩ := sub q h
    exact hA
  · intro q x y hx hy hhead hlead
    obtain ⟨_,⟨_,rfl⟩,tx⟩ := sub q hx
    obtain ⟨_,⟨_,rfl⟩,ty⟩ := sub q hy
    have same : recoveryInput i q.val.1 x.val (f x).val = recoveryInput i q.val.1 y.val (f y).val := by
      funext s k
      cases s
      · by_cases h : k = i
        · subst k
          simpa only [recoveryInput,Function.update_self] using hlead
        · simpa only [recoveryInput,Function.update_of_ne h] using hhead k h
      · exact k.elim
    exact tx.symm.trans ((congrArg (fun w => (realizeFieldTuple q.val.2 w) .vf) same).trans ty)

end GeneralizedEuler.Section5
