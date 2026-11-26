module

public import Section5.DefinableBijectionSchemes

/-! A fixed cardinality bound in a fiber is a first-order condition.
This allows a witness scheme to include the finite deletion bound. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P V : TCsort → Type}

@[expose] def FiberCardBound (D : Set (SortedAssignment X (SumVariables P V)))
    (m : ℕ) (p : SortedAssignment X P) : Prop :=
  ∀ a : Fin (m+1) → SortedAssignment X V, (∀ i, appendAssignments p (a i) ∈ D) → ¬ Function.Injective a

theorem FiberCardBound.finite {D : Set (SortedAssignment X (SumVariables P V))}
    {m : ℕ} {p : SortedAssignment X P} (h : FiberCardBound D m p) :
    {v | appendAssignments p v ∈ D}.Finite := by
  by_contra hf
  have hi : {v | appendAssignments p v ∈ D}.Infinite := hf
  let f := hi.natEmbedding
  let a (i : Fin (m+1)) := (f i.val).val
  have ha : Function.Injective a := fun _ _ eq => Fin.ext (f.injective (Subtype.ext eq))
  exact h a (fun i => (f i.val).property) ha

theorem fiberCardBound_definable [Finite (V .vf)] [Finite (V .rv)]
    {D : Set (SortedAssignment X (SumVariables P V))} (hD : SortedDefinableOver M S.carrier D) (m : ℕ) :
    SortedDefinableOver M S.carrier {p | FiberCardBound D m p} := by
  classical
  let N := Fin (m+1)
  let Block (s : TCsort) := N × V s
  let W := SumVariables P Block
  let slice (i : N) (s : TCsort) : SumVariables P V s → W s :=
    Sum.elim Sum.inl (fun v => .inr (i,v))
  have all := SortedDefinableOver.iInter (fun i : N => hD.pullback_relabel (slice i))
  let pairs := {ij : N × N // ij.1 ≠ ij.2}
  let same (i j : N) :=
    {x : SortedAssignment X W | (∀ v, x .vf (.inr (i,v)) = x .vf (.inr (j,v))) ∧
      (∀ v, x .rv (.inr (i,v)) = x .rv (.inr (j,v)))}
  have sameDef (i j : N) : SortedDefinableOver M S.carrier (same i j) := by
    have vf := SortedDefinableOver.iInter (fun v : V .vf =>
      SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .vf (.inr (i,v)) (.inr (j,v)))
    have rv := SortedDefinableOver.iInter (fun v : V .rv =>
      SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .rv (.inr (i,v)) (.inr (j,v)))
    convert vf.inter rv using 1
    ext x
    simp only [same,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  have distinct := SortedDefinableOver.iInter (fun k : pairs => (sameDef k.val.1 k.val.2).compl)
  have defined := (definable_project_mixed (all.inter distinct)).compl
  convert defined using 1
  ext p
  simp only [FiberCardBound,Set.mem_ofPred_eq,Set.mem_compl_iff,Set.mem_inter_iff,Set.mem_iInter]
  let unpack (b : SortedAssignment X Block) (i : N) : SortedAssignment X V := fun s v => b s (i,v)
  have pairEq (b : SortedAssignment X Block) (i j : N) :
      appendAssignments p b ∈ same i j ↔ unpack b i = unpack b j := by
    change ((∀ v, b .vf (i,v) = b .vf (j,v)) ∧ (∀ v, b .rv (i,v) = b .rv (j,v))) ↔ _
    exact ⟨fun ⟨hv,hr⟩ => by funext s v; cases s; exact hv v; exact hr v,
      fun e => ⟨fun v => congrFun (congrFun e .vf) v,fun v => congrFun (congrFun e .rv) v⟩⟩
  have allEq (b : SortedAssignment X Block) (i : N) :
      (fun s => appendAssignments p b s ∘ slice i s) = appendAssignments p (unpack b i) := by
    funext s v
    cases v <;> rfl
  have domain (b : SortedAssignment X Block) (i : N) :
      appendAssignments p b ∈ {x | (fun s => x s ∘ slice i s) ∈ D} ↔
        appendAssignments p (unpack b i) ∈ D := by
    change (fun s => appendAssignments p b s ∘ slice i s) ∈ D ↔ _
    rw [allEq]
  simp only [pairEq]
  constructor
  · intro h
    rintro ⟨b,hm,hs⟩
    apply h (unpack b) (fun i => (domain b i).1 (hm i))
    intro i j eq
    by_contra ne
    exact hs ⟨(i,j),ne⟩ eq
  · intro h a ha inj
    let b : SortedAssignment X Block := fun s iv => a iv.1 s iv.2
    exact h ⟨b,fun i => (domain b i).2 (ha i),fun ij eq => ij.property (inj eq)⟩

theorem FiberCardBound.mono {D : Set (SortedAssignment X (SumVariables P V))}
    {m n : ℕ} {p : SortedAssignment X P} (h : FiberCardBound D m p) (le : m ≤ n) :
    FiberCardBound D n p := by
  intro a ha inj
  let e (i : Fin (m+1)) : Fin (n+1) := ⟨i.val,i.isLt.trans_le (Nat.succ_le_succ le)⟩
  exact h (a ∘ e) (fun i => ha (e i))
    (inj.comp fun _ _ eq => Fin.ext (congrArg (fun v : Fin (n+1) => v.val) eq))

theorem fiberCardBound_of_finite {D : Set (SortedAssignment X (SumVariables P V))}
    {p : SortedAssignment X P} (fin : {v | appendAssignments p v ∈ D}.Finite) :
    ∃ m, FiberCardBound D m p := by
  let := fin.fintype
  let m := Fintype.card {v | appendAssignments p v ∈ D}
  refine ⟨m,?_⟩
  intro a ha inj
  let f (i : Fin (m+1)) : {v | appendAssignments p v ∈ D} := ⟨a i,ha i⟩
  have h := Fintype.card_le_of_injective f (fun _ _ eq => inj (congrArg Subtype.val eq))
  rw [Fintype.card_fin] at h
  exact Nat.not_succ_le_self m h

theorem uniform_finite_fiber_bound [Finite (V .vf)] [Finite (V .rv)]
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (B : Set (SortedAssignment X P)) (hB : SortedDefinableOver M S.carrier B)
    (D : Set (SortedAssignment X (SumVariables P V))) (hD : SortedDefinableOver M S.carrier D)
    (finite : ∀ p ∈ B, {v | appendAssignments p v ∈ D}.Finite) :
    ∃ m, ∀ p ∈ B, FiberCardBound D m p := by
  obtain ⟨C,hC⟩ := finite_definable_cover sat B hB (fun m => {p | FiberCardBound D m p})
    (fiberCardBound_definable hD) (fun p hp => fiberCardBound_of_finite (finite p hp))
  refine ⟨C.sup id,fun p hp => ?_⟩
  obtain ⟨m,hm,h⟩ := hC p hp
  exact h.mono (Finset.le_sup (f := id) hm)

end GeneralizedEuler.Section5
