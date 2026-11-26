module

public import Section5.RelativeRVObjectSchemes
public import Section5.GradedRVProducts
import all Section4.Objects

/-! Cartesian products of relative RV objects use concatenated tags
and labels. The product of the two bounds bounds the new fibers. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.RelativeRVObjectScheme

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}

@[expose] def leftRV (r t : ℕ) : ∀ s, RVVariables (Fin r) s → RVVariables (Fin (r+t)) s
  | .vf => PEmpty.elim
  | .rv => finSumFinEquiv ∘ Sum.inl

@[expose] def rightRV (r t : ℕ) : ∀ s, RVVariables (Fin t) s → RVVariables (Fin (r+t)) s
  | .vf => PEmpty.elim
  | .rv => finSumFinEquiv ∘ Sum.inr

private def splitRV (r t : ℕ) :
    labelAssignment (r+t) X ≃ labelAssignment r X × labelAssignment t X where
  toFun a := (fun s => a s ∘ leftRV r t s,fun s => a s ∘ rightRV r t s)
  invFun a := rvTupleAssignment (Sum.elim (a.1 .rv) (a.2 .rv) ∘ finSumFinEquiv.symm)
  left_inv a := by
    funext s i
    cases s with
    | vf => exact i.elim
    | rv =>
      obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
      simp only [rvTupleAssignment,Function.comp_apply,Equiv.symm_apply_apply,leftRV,rightRV]
      cases j <;> rfl
  right_inv a := by
    apply Prod.ext
    all_goals
      funext s i
      cases s with
      | vf => exact i.elim
      | rv =>
        simp only [leftRV,rightRV,rvTupleAssignment,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]

variable (A B : RelativeRVObjectScheme M S P)

@[expose] def cartesianProduct : RelativeRVObjectScheme M S P where
  data :=
    { degree := A.data.degree + B.data.degree
      arity := A.data.arity + B.data.arity
      tags := {u | (fun s => u s ∘ Sum.map id (leftRV A.data.arity B.data.arity s)) ∈ A.data.tags ∧
        (fun s => u s ∘ Sum.map id (rightRV A.data.arity B.data.arity s)) ∈ B.data.tags}
      definable := (A.data.definable.pullback_relabel (fun s => Sum.map id (leftRV _ _ s))).inter
        (B.data.definable.pullback_relabel (fun s => Sum.map id (rightRV _ _ s))) }
  graph := {u |
    (fun s => u s ∘ Sum.map (Sum.map id (leftRV A.data.arity B.data.arity s))
      (leftRV A.data.degree B.data.degree s)) ∈ A.graph ∧
    (fun s => u s ∘ Sum.map (Sum.map id (rightRV A.data.arity B.data.arity s))
      (rightRV A.data.degree B.data.degree s)) ∈ B.graph}
  definable := (A.definable.pullback_relabel (fun s => Sum.map (Sum.map id (leftRV _ _ s)) (leftRV _ _ s))).inter
    (B.definable.pullback_relabel (fun s => Sum.map (Sum.map id (rightRV _ _ s)) (rightRV _ _ s)))
  bound := A.bound * B.bound

private theorem append_split_tags {r t : ℕ} (p : SortedAssignment X P) (u : labelAssignment (r+t) X) :
    (fun s => appendAssignments p u s ∘ Sum.map id (leftRV r t s)) = appendAssignments p ((splitRV r t u).1) := by
  funext s i
  cases i <;> rfl

private theorem append_split_tags_right {r t : ℕ} (p : SortedAssignment X P) (u : labelAssignment (r+t) X) :
    (fun s => appendAssignments p u s ∘ Sum.map id (rightRV r t s)) = appendAssignments p ((splitRV r t u).2) := by
  funext s i
  cases i <;> rfl

private theorem product_tags (p : SortedAssignment X P) (u : labelAssignment (A.data.arity + B.data.arity) X) :
    appendAssignments p u ∈ (A.cartesianProduct B).data.tags ↔
      appendAssignments p ((splitRV _ _ u).1) ∈ A.data.tags ∧
      appendAssignments p ((splitRV _ _ u).2) ∈ B.data.tags := by
  change ((fun s => appendAssignments p u s ∘ Sum.map id (leftRV _ _ s)) ∈ A.data.tags ∧
    (fun s => appendAssignments p u s ∘ Sum.map id (rightRV _ _ s)) ∈ B.data.tags) ↔ _
  rw [append_split_tags,append_split_tags_right]

private theorem product_graph (p : SortedAssignment X P)
    (u : labelAssignment (A.data.arity + B.data.arity) X) (v : labelAssignment (A.data.degree + B.data.degree) X) :
    appendAssignments (appendAssignments p u) v ∈ (A.cartesianProduct B).graph ↔
      appendAssignments (appendAssignments p ((splitRV _ _ u).1)) ((splitRV _ _ v).1) ∈ A.graph ∧
      appendAssignments (appendAssignments p ((splitRV _ _ u).2)) ((splitRV _ _ v).2) ∈ B.graph := by
  have left : (fun s => appendAssignments (appendAssignments p u) v s ∘
      Sum.map (Sum.map id (leftRV _ _ s)) (leftRV _ _ s)) =
      appendAssignments (appendAssignments p ((splitRV _ _ u).1)) ((splitRV _ _ v).1) := by
    funext s i
    rcases i with (i|i)|i <;> rfl
  have right : (fun s => appendAssignments (appendAssignments p u) v s ∘
      Sum.map (Sum.map id (rightRV _ _ s)) (rightRV _ _ s)) =
      appendAssignments (appendAssignments p ((splitRV _ _ u).2)) ((splitRV _ _ v).2) := by
    funext s i
    rcases i with (i|i)|i <;> rfl
  change (_ ∧ _) ↔ _
  rw [left,right]

@[expose] def productCoordsLeft (s : TCsort) :
    MixedVariables A.data.degree (Fin A.data.arity) s →
      MixedVariables (A.data.degree+B.data.degree) (Fin (A.data.arity+B.data.arity)) s :=
  match s with
  | .vf => finSumFinEquiv ∘ Sum.inl
  | .rv => finSumFinEquiv ∘ Sum.inl

@[expose] def productCoordsRight (s : TCsort) :
    MixedVariables B.data.degree (Fin B.data.arity) s →
      MixedVariables (A.data.degree+B.data.degree) (Fin (A.data.arity+B.data.arity)) s :=
  match s with
  | .vf => finSumFinEquiv ∘ Sum.inr
  | .rv => finSumFinEquiv ∘ Sum.inr

theorem cartesianProduct_lift_mem (p : SortedAssignment X P)
    (x : SortedAssignment X (MixedVariables (A.data.degree+B.data.degree) (Fin (A.data.arity+B.data.arity)))) :
    appendAssignments p x ∈ relativeRVLift (M := M) (A.cartesianProduct B).graph ↔
      appendAssignments p (fun s => x s ∘ A.productCoordsLeft B s) ∈ relativeRVLift (M := M) A.graph ∧
      appendAssignments p (fun s => x s ∘ A.productCoordsRight B s) ∈ relativeRVLift (M := M) B.graph := by
  have h := A.product_graph B p (rvTupleAssignment (x .rv)) (rvTupleAssignment (M.rvMap ∘ x .vf))
  have tagL : (splitRV A.data.arity B.data.arity (rvTupleAssignment (x .rv))).1 =
      rvTupleAssignment ((fun s => x s ∘ A.productCoordsLeft B s) .rv) := by
    funext s i
    cases s with | vf => exact i.elim | rv => rfl
  have tagR : (splitRV A.data.arity B.data.arity (rvTupleAssignment (x .rv))).2 =
      rvTupleAssignment ((fun s => x s ∘ A.productCoordsRight B s) .rv) := by
    funext s i
    cases s with | vf => exact i.elim | rv => rfl
  have valueL : (splitRV A.data.degree B.data.degree (rvTupleAssignment (M.rvMap ∘ x .vf))).1 =
      rvTupleAssignment (M.rvMap ∘ (fun s => x s ∘ A.productCoordsLeft B s) .vf) := by
    funext s i
    cases s with | vf => exact i.elim | rv => rfl
  have valueR : (splitRV A.data.degree B.data.degree (rvTupleAssignment (M.rvMap ∘ x .vf))).2 =
      rvTupleAssignment (M.rvMap ∘ (fun s => x s ∘ A.productCoordsRight B s) .vf) := by
    funext s i
    cases s with | vf => exact i.elim | rv => rfl
  rw [tagL,tagR,valueL,valueR] at h
  exact h

private theorem fiber_card_bound (C : RelativeRVObjectScheme M S P)
    {p : SortedAssignment X P} {zero : S.carrier .rv} (valid : C.valid zero p)
    (v : labelAssignment C.data.degree X)
    (F : Set (labelAssignment C.data.arity X))
    (f : ∀ u, u ∈ F ↔ appendAssignments (appendAssignments p u) v ∈ C.graph) :
    Nat.card F ≤ C.bound := by
  classical
  let : Finite F := (valid.finite_fiber v).subset (fun _ h => (f _).1 h)
  let : Fintype F := Fintype.ofFinite F
  by_contra! tooMany
  have enough : C.bound + 1 ≤ Fintype.card F := Nat.succ_le_of_lt (Nat.card_eq_fintype_card (α := F) ▸ tooMany)
  let e := (Fin.castLEEmb enough).trans (Fintype.equivFin F).symm.toEmbedding
  exact (valid.2.2.2 v (fun i => (e i).val) (fun i => (f _).1 (e i).property))
    (fun i j h => e.injective (Subtype.ext h))

theorem cartesianProduct_valid {p : SortedAssignment X P} {zero : S.carrier .rv}
    (a : A.valid zero p) (b : B.valid zero p) : (A.cartesianProduct B).valid zero p := by
  classical
  let split := splitRV (X := X) A.data.arity B.data.arity
  let labels := splitRV (X := X) A.data.degree B.data.degree
  refine ⟨?_,?_,?_,?_⟩
  · intro u
    constructor
    · intro hu
      obtain ⟨ha,hb⟩ := (A.product_tags B p u).1 hu
      obtain ⟨v,hv⟩ := (a.1 _).1 ha
      obtain ⟨w,hw⟩ := (b.1 _).1 hb
      refine ⟨labels.symm (v,w),(A.product_graph B p u _).2 ?_⟩
      change appendAssignments (appendAssignments p (split u).1) (labels (labels.symm (v,w))).1 ∈ A.graph ∧
        appendAssignments (appendAssignments p (split u).2) (labels (labels.symm (v,w))).2 ∈ B.graph
      rw [labels.apply_symm_apply]
      exact ⟨hv,hw⟩
    · rintro ⟨v, hv⟩
      obtain ⟨ha,hb⟩ := (A.product_graph B p u v).1 hv
      exact (A.product_tags B p u).2 ⟨(a.1 _).2 ⟨_,ha⟩,(b.1 _).2 ⟨_,hb⟩⟩
  · intro u v w hv hw
    have h₁ := (A.product_graph B p u v).1 hv
    have h₂ := (A.product_graph B p u w).1 hw
    exact labels.injective (Prod.ext (a.2.1 _ _ _ h₁.1 h₂.1) (b.2.1 _ _ _ h₁.2 h₂.2))
  · intro u v hv j
    obtain ⟨ha,hb⟩ := (A.product_graph B p u v).1 hv
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    rcases j with j|j
    · exact a.2.2.1 _ _ ha j
    · exact b.2.2.1 _ _ hb j
  · intro v f hf inj
    let F := {u | appendAssignments (appendAssignments p u) (labels v).1 ∈ A.graph}
    let G := {u | appendAssignments (appendAssignments p u) (labels v).2 ∈ B.graph}
    let g (i : Fin ((A.cartesianProduct B).bound + 1)) : F × G :=
      let h := (A.product_graph B p (f i) v).1 (hf i)
      (⟨(split (f i)).1,h.1⟩,⟨(split (f i)).2,h.2⟩)
    have ginj : Function.Injective g := fun _ _ eq => inj (split.injective (Prod.ext
      (congrArg (fun a : F × G => a.1.val) eq) (congrArg (fun a : F × G => a.2.val) eq)))
    have fcard := fiber_card_bound A a (labels v).1 F (fun _ => Iff.rfl)
    have gcard := fiber_card_bound B b (labels v).2 G (fun _ => Iff.rfl)
    let : Finite F := a.finite_fiber (labels v).1
    let : Finite G := b.finite_fiber (labels v).2
    let : Fintype F := Fintype.ofFinite F
    let : Fintype G := Fintype.ofFinite G
    have le := Fintype.card_le_of_injective g ginj
    rw [Fintype.card_fin,Fintype.card_prod,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at le
    exact (Nat.not_succ_le_self _) (le.trans (Nat.mul_le_mul fcard gcard))

theorem cartesianProduct_realize_class
    {p : SortedAssignment X P} {zero : S.carrier .rv}
    (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (a : A.valid zero p) (b : B.valid zero p) :
    let T := M.termGenerated (namedTuple S p)
    objectClass M T ⟨(A.cartesianProduct B).data.degree,
      (A.cartesianProduct B).realize zero hzero p (A.cartesianProduct_valid B a b)⟩ =
      objectClass M T ⟨A.data.degree,A.realize zero hzero p a⟩ *
      objectClass M T ⟨B.data.degree,B.realize zero hzero p b⟩ := by
  intro T
  let U := A.realize zero hzero p a
  let V := B.realize zero hzero p b
  let W := (A.cartesianProduct B).realize zero hzero p (A.cartesianProduct_valid B a b)
  have carriers : W.carrier = (RVObject.cartesianProduct U V).carrier := by
    ext t
    have tag := A.product_tags B p (rvTupleAssignment t)
    change appendAssignments p (rvTupleAssignment t) ∈ (A.cartesianProduct B).data.tags ↔
      t ∘ finSumFinEquiv ∘ Sum.inl ∈ U.carrier ∧ t ∘ finSumFinEquiv ∘ Sum.inr ∈ V.carrier
    have left : (splitRV A.data.arity B.data.arity (rvTupleAssignment t)).1 =
        rvTupleAssignment (t ∘ finSumFinEquiv ∘ Sum.inl) := by
      funext s i
      cases s with | vf => exact i.elim | rv => rfl
    have right : (splitRV A.data.arity B.data.arity (rvTupleAssignment t)).2 =
        rvTupleAssignment (t ∘ finSumFinEquiv ∘ Sum.inr) := by
      funext s i
      cases s with | vf => exact i.elim | rv => rfl
    rw [left,right] at tag
    exact tag
  have iso : RVDefinablyEquivalent M T.carrier W.carrier (RVObject.cartesianProduct U V).carrier := by
    rw [carriers]
    exact ⟨Equiv.refl _,definable_identity_label M T (RVObject.cartesianProduct U V).definable⟩
  exact (scissors_sound M T (.iso _ _ iso)).trans (RVObject.cartesianProduct_class U V)

end GeneralizedEuler.Section5.RelativeRVObjectScheme
