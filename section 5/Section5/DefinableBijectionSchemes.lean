module

public import Section5.DefinableCovers

/-! The parameters where a fixed graph is a bijection between two
specified fibers form a definable set. This gives one of the validity
tests for choosing fiberwise witnesses uniformly. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P U V : TCsort → Type}

abbrev appendAssignments (x : SortedAssignment X U) (y : SortedAssignment X V) :
    SortedAssignment X (SumVariables U V) := fun s => Sum.elim (x s) (y s)

theorem definable_forall_assignments [Finite (V .vf)] [Finite (V .rv)]
    {D : Set (SortedAssignment X (SumVariables U V))} (hd : SortedDefinableOver M S.carrier D) :
    SortedDefinableOver M S.carrier {x | ∀ y, appendAssignments x y ∈ D} := by
  classical
  have h := (definable_project_mixed hd.compl).compl
  convert h using 1
  ext x
  exact not_exists_not.symm

theorem definable_forall_iff_exists [Finite (U .vf)] [Finite (U .rv)]
    [Finite (V .vf)] [Finite (V .rv)]
    (A : Set (SortedAssignment X (SumVariables P U)))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (ha : SortedDefinableOver M S.carrier A) (hg : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier {p | ∀ u, appendAssignments p u ∈ A ↔
      ∃ v, appendAssignments (appendAssignments p u) v ∈ G} := by
  classical
  have existsV := definable_project_mixed hg
  have agrees := (ha.inter existsV).union (ha.compl.inter existsV.compl)
  convert definable_forall_assignments agrees using 1
  ext p
  symm
  change (∀ u, (_ ∧ _) ∨ (¬ _ ∧ ¬ _)) ↔ (∀ u, _ ↔ _)
  exact forall_congr' fun u => ⟨fun h => h.elim (fun h => iff_of_true h.1 h.2)
    (fun h => iff_of_false h.1 h.2),fun h => by
      by_cases ha' : appendAssignments p u ∈ A
      · exact Or.inl ⟨ha',h.1 ha'⟩
      · exact Or.inr ⟨ha',fun e => ha' (h.2 e)⟩⟩

theorem definable_fiberwise_functional [Finite (U .vf)] [Finite (U .rv)]
    [Finite (V .vf)] [Finite (V .rv)]
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (hg : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier {p | ∀ u v w,
      appendAssignments (appendAssignments p u) v ∈ G →
      appendAssignments (appendAssignments p u) w ∈ G → v = w} := by
  let W := SumVariables (SumVariables (SumVariables P U) V) V
  let first (s : TCsort) : SumVariables (SumVariables P U) V s → W s := Sum.inl
  let second (s : TCsort) : SumVariables (SumVariables P U) V s → W s :=
    Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have equalVF := SortedDefinableOver.iInter (fun i : V .vf =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .vf (.inl (.inr i)) (.inr i))
  have equalRV := SortedDefinableOver.iInter (fun i : V .rv =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .rv (.inl (.inr i)) (.inr i))
  have condition := (((hg.pullback_relabel first).inter (hg.pullback_relabel second)).compl).union
    (equalVF.inter equalRV)
  convert definable_forall_assignments (definable_forall_assignments
    (definable_forall_assignments condition)) using 1
  ext p
  symm
  simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,Set.mem_inter_iff,Set.mem_iInter]
  let g (u : SortedAssignment X U) (v : SortedAssignment X V) :=
    appendAssignments (appendAssignments p u) v ∈ G
  let args (u : SortedAssignment X U) (v w : SortedAssignment X V) :=
    appendAssignments (appendAssignments (appendAssignments p u) v) w
  have fstEq u v w : (fun s => args u v w s ∘ first s) = appendAssignments (appendAssignments p u) v := by
    funext s i
    rfl
  have sndEq u v w : (fun s => args u v w s ∘ second s) = appendAssignments (appendAssignments p u) w := by
    funext s i
    rcases i with i | i <;> rfl
  change (∀ u v w, ¬ ((fun s => args u v w s ∘ first s) ∈ G ∧
      (fun s => args u v w s ∘ second s) ∈ G) ∨
      ((∀ i, v .vf i = w .vf i) ∧ (∀ i, v .rv i = w .rv i))) ↔
    (∀ u v w, g u v → g u w → v = w)
  simp only [fstEq,sndEq]
  constructor
  · intro h u v w hv hw
    rcases h u v w with hbad | ⟨hvf,hrv⟩
    · exact False.elim (hbad ⟨hv,hw⟩)
    · funext s i
      cases s
      · exact hvf i
      · exact hrv i
  · intro h u v w
    classical
    by_cases hboth : appendAssignments (appendAssignments p u) v ∈ G ∧
        appendAssignments (appendAssignments p u) w ∈ G
    · have eq := h u v w hboth.1 hboth.2
      subst w
      exact Or.inr ⟨fun _ => rfl,fun _ => rfl⟩
    · exact Or.inl hboth

@[expose] def FiberBijectionScheme
    (A : Set (SortedAssignment X (SumVariables P U)))
    (B : Set (SortedAssignment X (SumVariables P V)))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (p : SortedAssignment X P) : Prop :=
  (∀ u, appendAssignments p u ∈ A ↔ ∃ v, appendAssignments (appendAssignments p u) v ∈ G) ∧
  (∀ v, appendAssignments p v ∈ B ↔ ∃ u, appendAssignments (appendAssignments p u) v ∈ G) ∧
  (∀ u v w, appendAssignments (appendAssignments p u) v ∈ G →
    appendAssignments (appendAssignments p u) w ∈ G → v = w) ∧
  (∀ v u w, appendAssignments (appendAssignments p u) v ∈ G →
    appendAssignments (appendAssignments p w) v ∈ G → u = w)

theorem fiberBijectionScheme_definable [Finite (U .vf)] [Finite (U .rv)]
    [Finite (V .vf)] [Finite (V .rv)]
    {A : Set (SortedAssignment X (SumVariables P U))}
    {B : Set (SortedAssignment X (SumVariables P V))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (ha : SortedDefinableOver M S.carrier A) (hb : SortedDefinableOver M S.carrier B)
    (hg : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier {p | FiberBijectionScheme A B G p} := by
  let swap (s : TCsort) : SumVariables (SumVariables P U) V s → SumVariables (SumVariables P V) U s
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr i
    | .inr i => .inl (.inr i)
  let H : Set (SortedAssignment X (SumVariables (SumVariables P V) U)) :=
    {x | (fun s => x s ∘ swap s) ∈ G}
  have hw : SortedDefinableOver M S.carrier H := hg.pullback_relabel swap
  have eq p u v : appendAssignments (appendAssignments p v) u ∈ H ↔
      appendAssignments (appendAssignments p u) v ∈ G := by
    have same : (fun s => (appendAssignments (appendAssignments p v) u) s ∘ swap s) =
        appendAssignments (appendAssignments p u) v := by
      funext s i
      rcases i with (i | i) | i <;> rfl
    change (fun s => (appendAssignments (appendAssignments p v) u) s ∘ swap s) ∈ G ↔ _
    rw [same]
  have domains := definable_forall_iff_exists A G ha hg
  have ranges := definable_forall_iff_exists B H hb hw
  have functional := definable_fiberwise_functional G hg
  have injective := definable_fiberwise_functional H hw
  convert domains.inter (ranges.inter (functional.inter injective)) using 1
  ext p
  simp only [FiberBijectionScheme,Set.mem_ofPred_eq,Set.mem_inter_iff,eq]

noncomputable def FiberBijectionScheme.equiv
    {A : Set (SortedAssignment X (SumVariables P U))}
    {B : Set (SortedAssignment X (SumVariables P V))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    {p : SortedAssignment X P} (h : FiberBijectionScheme A B G p) :
    {u : SortedAssignment X U | appendAssignments p u ∈ A} ≃
      {v : SortedAssignment X V | appendAssignments p v ∈ B} := by
  classical
  let source (u : SortedAssignment X U) := appendAssignments p u ∈ A
  let target (v : SortedAssignment X V) := appendAssignments p v ∈ B
  let graph (u : SortedAssignment X U) (v : SortedAssignment X V) :=
    appendAssignments (appendAssignments p u) v ∈ G
  let f (u : Subtype source) : Subtype target :=
    let hv := (h.1 u.val).1 u.property
    ⟨hv.choose,(h.2.1 hv.choose).2 ⟨u.val,hv.choose_spec⟩⟩
  have hf (u : Subtype source) : graph u.val (f u).val := ((h.1 u.val).1 u.property).choose_spec
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b eq
    exact Subtype.ext (h.2.2.2 (f a).val _ _ (hf a) (eq.symm ▸ hf b))
  · intro b
    obtain ⟨a,ha⟩ := (h.2.1 b.val).1 b.property
    let u : Subtype source := ⟨a,(h.1 a).2 ⟨b.val,ha⟩⟩
    exact ⟨u,Subtype.ext (h.2.2.1 u.val _ _ (hf u) ha)⟩

end GeneralizedEuler.Section5
