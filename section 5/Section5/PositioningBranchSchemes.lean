module

public import Section5.GeneratedParameterSchemes
public import Section5.DefinableCovers
public import Section5.LiftBoundaryDimension

/-! The constant and injective branches of a unary positioning graph
are first-order tests over the original base. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}

local notation "U" => MixedVariables 1 Empty
local notation "PV" => SumVariables P U
local notation "PVV" => SumVariables PV U

@[expose] def constantPositioning
    (C : Set (SortedAssignment X PV)) (G : Set (SortedAssignment X PVV)) (p : SortedAssignment X P) : Prop :=
  ∀ (a b c d : SortedAssignment X U),
    appendAssignments p a ∈ C → appendAssignments p c ∈ C →
    appendAssignments (appendAssignments p a) b ∈ G →
    appendAssignments (appendAssignments p c) d ∈ G → b = d

@[expose] def injectivePositioning
    (C : Set (SortedAssignment X PV)) (G : Set (SortedAssignment X PVV)) (p : SortedAssignment X P) : Prop :=
  ∀ (a b c d : SortedAssignment X U),
    appendAssignments p a ∈ C → appendAssignments p c ∈ C →
    appendAssignments (appendAssignments p a) b ∈ G →
    appendAssignments (appendAssignments p c) d ∈ G → b = d → a = c

theorem positioning_branch_tests_definable
    {C : Set (SortedAssignment X PV)} (defC : SortedDefinableOver M S.carrier C)
    {G : Set (SortedAssignment X PVV)} (defG : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier {p | constantPositioning C G p} ∧
      SortedDefinableOver M S.carrier {p | injectivePositioning C G p} := by
  let T := SumVariables (SumVariables PVV U) U
  let left (s : TCsort) : PVV s → T s := Sum.inl ∘ Sum.inl
  let right (s : TCsort) : PVV s → T s :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr)) Sum.inr
  have valid := defG.inter (defC.pullback_relabel (fun _ => Sum.inl))
  have both := (valid.pullback_relabel left).inter (valid.pullback_relabel right)
  have eqX := SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := T)
    .vf (.inl (.inl (.inl (.inr 0)))) (.inl (.inr 0))
  have eqY := SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := T)
    .vf (.inl (.inl (.inr 0))) (.inr 0)
  let all {D : Set (SortedAssignment X T)} (defD : SortedDefinableOver M S.carrier D) :=
    definable_forall_assignments (definable_forall_assignments (definable_forall_assignments
      (definable_forall_assignments defD)))
  have eval (p : SortedAssignment X P) (a b c d : SortedAssignment X U) :
      (fun s => appendAssignments (appendAssignments (appendAssignments (appendAssignments p a) b) c) d s ∘ right s) =
        appendAssignments (appendAssignments p c) d := by
    funext s i
    rcases i with (i | i) | i <;> rfl
  have evalInput (p : SortedAssignment X P) (a b c d : SortedAssignment X U) :
      (fun s => (appendAssignments (appendAssignments (appendAssignments (appendAssignments p a) b) c) d s ∘ right s) ∘ Sum.inl) =
        appendAssignments p c :=
    congrArg (fun (x : SortedAssignment X PVV) s => x s ∘ Sum.inl) (eval p a b c d)
  have eq₁ (a c : SortedAssignment X U) : a .vf 0 = c .vf 0 ↔ a = c :=
    ⟨fun eq => fieldAssignment_ext (fun i => by
      rw [Subsingleton.elim i (0 : Fin 1)]
      exact eq),fun e => congrFun (congrFun e .vf) 0⟩
  constructor
  · convert all (both.compl.union eqY) using 1
    ext p
    simp only [constantPositioning,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_union]
    refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun c => forall_congr' fun d => ?_
    change (appendAssignments p a ∈ C → appendAssignments p c ∈ C →
      appendAssignments (appendAssignments p a) b ∈ G → appendAssignments (appendAssignments p c) d ∈ G → b = d) ↔
        (¬ ((appendAssignments (appendAssignments p a) b ∈ G ∧ appendAssignments p a ∈ C) ∧
          ((fun s => appendAssignments (appendAssignments (appendAssignments (appendAssignments p a) b) c) d s ∘ right s) ∈ G ∧
            (fun s => (appendAssignments (appendAssignments (appendAssignments (appendAssignments p a) b) c) d s ∘ right s) ∘ Sum.inl) ∈ C)) ∨
          b .vf 0 = d .vf 0)
    rw [eval,evalInput]
    simp only [eq₁]
    tauto
  · convert all ((both.inter eqY).compl.union eqX) using 1
    ext p
    simp only [injectivePositioning,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_union]
    refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun c => forall_congr' fun d => ?_
    change (appendAssignments p a ∈ C → appendAssignments p c ∈ C →
      appendAssignments (appendAssignments p a) b ∈ G → appendAssignments (appendAssignments p c) d ∈ G →
        b = d → a = c) ↔
        (¬ (((appendAssignments (appendAssignments p a) b ∈ G ∧ appendAssignments p a ∈ C) ∧
          ((fun s => appendAssignments (appendAssignments (appendAssignments (appendAssignments p a) b) c) d s ∘ right s) ∈ G ∧
            (fun s => (appendAssignments (appendAssignments (appendAssignments (appendAssignments p a) b) c) d s ∘ right s) ∘ Sum.inl) ∈ C)) ∧
          b .vf 0 = d .vf 0) ∨ a .vf 0 = c .vf 0)
    rw [eval,evalInput]
    simp only [eq₁]
    tauto

structure PositioningBranchScheme (M : SortedStructure L E X) (S : SortedSubstructure M) (P : TCsort → Type) where
  count : ℕ
  pieces : Fin count → Set (SortedAssignment X (SumVariables P (MixedVariables 1 Empty)))
  definable : ∀ i, SortedDefinableOver M S.carrier (pieces i)

namespace PositioningBranchScheme

@[expose] def valid (W : PositioningBranchScheme M S P)
    (A : Set (SortedAssignment X (SumVariables P (MixedVariables 1 Empty))))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P (MixedVariables 1 Empty)) (MixedVariables 1 Empty))))
    (p : SortedAssignment X P) : Prop :=
  (∀ a : SortedAssignment X (MixedVariables 1 Empty), appendAssignments p a ∈ A ↔ ∃ i, appendAssignments p a ∈ W.pieces i) ∧
  (∀ i j : Fin W.count, i ≠ j → ∀ a : SortedAssignment X (MixedVariables 1 Empty),
    ¬ (appendAssignments p a ∈ W.pieces i ∧ appendAssignments p a ∈ W.pieces j)) ∧
  ∀ i, constantPositioning (W.pieces i) G p ∨ injectivePositioning (W.pieces i) G p

theorem valid_definable (W : PositioningBranchScheme M S P)
    (A : Set (SortedAssignment X (SumVariables P (MixedVariables 1 Empty))))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P (MixedVariables 1 Empty)) (MixedVariables 1 Empty))))
    (defA : SortedDefinableOver M S.carrier A) (defG : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier {p : SortedAssignment X P | W.valid A G p} := by
  let D := ⋃ i, W.pieces i
  have hd : SortedDefinableOver M S.carrier D := SortedDefinableOver.iUnion W.definable
  have cov := definable_forall_assignments ((defA.inter hd).union (defA.compl.inter hd.compl))
  let Distinct := {q : Fin W.count × Fin W.count // q.1 ≠ q.2}
  have disj := SortedDefinableOver.iInter (fun i : Distinct =>
    definable_forall_assignments ((W.definable i.val.1).inter (W.definable i.val.2)).compl)
  have choices := SortedDefinableOver.iInter (fun i =>
    (positioning_branch_tests_definable (W.definable i) defG).1.union
      (positioning_branch_tests_definable (W.definable i) defG).2)
  convert cov.inter (disj.inter choices) using 1
  ext p
  simp only [valid,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_union,Set.mem_compl_iff,D,Set.mem_iUnion]
  constructor
  · rintro ⟨hcov,hdisj,hclass⟩
    refine ⟨?_,fun q a => hdisj q.val.1 q.val.2 q.property a,hclass⟩
    intro a
    classical
    by_cases h : appendAssignments p a ∈ A
    · exact Or.inl ⟨h,(hcov a).1 h⟩
    · exact Or.inr ⟨h,fun e => h ((hcov a).2 e)⟩
  · rintro ⟨hcov,hdisj,hclass⟩
    refine ⟨?_,fun i j ne a => hdisj ⟨(i,j),ne⟩ a,hclass⟩
    intro a
    exact (hcov a).elim (fun h => iff_of_true h.1 h.2) (fun h => iff_of_false h.1 h.2)

end PositioningBranchScheme

theorem positioning_branch_scheme_of_generated_partition
    (p : SortedAssignment X P) {n : ℕ}
    (A : Set (SortedAssignment X PV)) (G : Set (SortedAssignment X PVV))
    (C : Fin n → Set (SortedAssignment X U))
    (defC : ∀ i, SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier (C i))
    (covers : ∀ a, appendAssignments p a ∈ A ↔ ∃ i, a ∈ C i)
    (disjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (branches : ∀ i,
      (∀ a b c d : SortedAssignment X U, a ∈ C i → c ∈ C i →
        appendAssignments (appendAssignments p a) b ∈ G → appendAssignments (appendAssignments p c) d ∈ G → b = d) ∨
      (∀ a b c d : SortedAssignment X U, a ∈ C i → c ∈ C i →
        appendAssignments (appendAssignments p a) b ∈ G → appendAssignments (appendAssignments p c) d ∈ G → b = d → a = c)) :
    ∃ W : PositioningBranchScheme M S P, W.valid A G p := by
  classical
  choose D defD fiberEq using fun i => definable_fiber_as_scheme p (C i) (defC i)
  let W : PositioningBranchScheme M S P := ⟨n,D,defD⟩
  refine ⟨W,?_,?_,?_⟩
  · intro a
    simpa only [W,fiberEq] using covers a
  · intro i j ne a
    simp only [W,fiberEq]
    exact fun h => Set.disjoint_left.1 (disjoint ne) h.1 h.2
  · intro i
    simpa only [W,constantPositioning,injectivePositioning,fiberEq] using branches i

theorem uniform_positioning_branch_schemes
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (D : Set (SortedAssignment X P)) (defD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X PV)) (defA : SortedDefinableOver M S.carrier A)
    (G : Set (SortedAssignment X PVV)) (defG : SortedDefinableOver M S.carrier G)
    (pointwise : ∀ p ∈ D, ∃ W : PositioningBranchScheme M S P, W.valid A G p) :
    ∃ (C : Finset (PositioningBranchScheme M S P)) (pieces : {i // i ∈ C} → Set (SortedAssignment X P)),
      (∀ i, SortedDefinableOver M S.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid A G p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D :=
  finite_definable_partition_of_cover sat D defD (fun i : PositioningBranchScheme M S P => {p | i.valid A G p})
    (fun i => i.valid_definable A G defA defG) pointwise

end GeneralizedEuler.Section5
