module

public import Section5.RelativeRVWitnesses
public import Section5.RVObjectFromGraph

/-! Glue an RV row over an RV index. Selected index coordinates join
the active label and the entire index stays in the carrier. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h m t k : ℕ}

local notation "P" => RVVariables (Fin h)
local notation "U" => RVVariables (Fin m)
local notation "V" => RVVariables (Fin k)

abbrev rvHead {a b : ℕ} : Fin a → Fin (a+b) := finSumFinEquiv ∘ Sum.inl
abbrev rvTail {a b : ℕ} : Fin b → Fin (a+b) := finSumFinEquiv ∘ Sum.inr

@[expose] def concatRV {a b : ℕ} (x : Fin a → X .rv) (y : Fin b → X .rv) : Fin (a+b) → X .rv :=
  Sum.elim x y ∘ finSumFinEquiv.symm

@[simp] theorem concatRV_head {a b : ℕ} (x : Fin a → X .rv) (y : Fin b → X .rv) :
    concatRV x y ∘ rvHead = x := by
  funext i
  simp [concatRV,Function.comp_def]

@[simp] theorem concatRV_tail {a b : ℕ} (x : Fin a → X .rv) (y : Fin b → X .rv) :
    concatRV x y ∘ rvTail = y := by
  funext i
  simp [concatRV,Function.comp_def]

theorem concatRV_split {a b : ℕ} (v : Fin (a+b) → X .rv) :
    concatRV (v ∘ rvHead) (v ∘ rvTail) = v := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => exact congrFun (concatRV_head _ _) j
  | inr j => exact congrFun (concatRV_tail _ _) j

@[expose] def gluedRVTags (B : Set (Fin h → X .rv))
    (D : Set (SortedAssignment X (SumVariables P U))) : Set (Fin (h+m) → X .rv) :=
  {u | u ∘ rvHead ∈ B ∧ appendAssignments (rvTupleAssignment (u ∘ rvHead))
    (rvTupleAssignment (u ∘ rvTail)) ∈ D}

theorem gluedRVTags_definable
    {B : Set (Fin h → X .rv)} (defB : isRVSet M S B)
    {D : Set (SortedAssignment X (SumVariables P U))} (defD : SortedDefinableOver M S.carrier D) :
    isRVSet M S (gluedRVTags B D) := by
  let old : (s : TCsort) → SumVariables P U s → RVVariables (Fin (h+m)) s
    | .vf => Sum.elim PEmpty.elim PEmpty.elim
    | .rv => finSumFinEquiv
  let base : (s : TCsort) → P s → RVVariables (Fin (h+m)) s
    | .vf => PEmpty.elim
    | .rv => rvHead
  unfold isRVSet at defB ⊢
  convert (defB.pullback_relabel base).inter (defD.pullback_relabel old) using 1
  ext a
  have eq : (fun s => a s ∘ old s) =
      appendAssignments (rvTupleAssignment (a .rv ∘ rvHead)) (rvTupleAssignment (a .rv ∘ rvTail)) := by
    funext s i
    rcases i with i | i
    · cases s
      · exact i.elim
      · rfl
    · cases s
      · exact i.elim
      · rfl
  change (_ ∧ _) ↔ (a .rv ∘ rvHead ∈ B ∧ (fun s => a s ∘ old s) ∈ D)
  rw [eq]

@[expose] def gluedRVGraph (sel : Fin t → Fin h) (B : Set (Fin h → X .rv))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))) :
    Set (SortedAssignment X (RVVariables (Fin (h+m) ⊕ Fin (t+k)))) :=
  {a | let u := a .rv ∘ Sum.inl
       let v := a .rv ∘ Sum.inr
       u ∘ rvHead ∈ B ∧ v ∘ rvHead = (u ∘ rvHead) ∘ sel ∧
        appendAssignments (appendAssignments (rvTupleAssignment (u ∘ rvHead)) (rvTupleAssignment (u ∘ rvTail)))
          (rvTupleAssignment (v ∘ rvTail)) ∈ G}

theorem gluedRVGraph_definable (sel : Fin t → Fin h)
    {B : Set (Fin h → X .rv)} (defB : isRVSet M S B)
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (defG : SortedDefinableOver M S.carrier G) :
    SortedDefinableOver M S.carrier (gluedRVGraph sel B G) := by
  let W := RVVariables (Fin (h+m) ⊕ Fin (t+k))
  let old : (s : TCsort) → SumVariables (SumVariables P U) V s → W s
    | .vf => Sum.elim (Sum.elim PEmpty.elim PEmpty.elim) PEmpty.elim
    | .rv => Sum.elim (Sum.inl ∘ finSumFinEquiv) (Sum.inr ∘ rvTail)
  let base : (s : TCsort) → P s → W s
    | .vf => PEmpty.elim
    | .rv => Sum.inl ∘ rvHead
  have head := SortedDefinableOver.iInter (fun i : Fin t =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := W) .rv
      (.inr (rvHead i)) (.inl (rvHead (sel i))))
  unfold isRVSet at defB
  convert (defB.pullback_relabel base).inter (head.inter (defG.pullback_relabel old)) using 1
  ext a
  let u := a .rv ∘ Sum.inl
  let v := a .rv ∘ Sum.inr
  have eq : (fun s => a s ∘ old s) =
      appendAssignments (appendAssignments (rvTupleAssignment (u ∘ rvHead)) (rvTupleAssignment (u ∘ rvTail)))
        (rvTupleAssignment (v ∘ rvTail)) := by
    funext s i
    rcases i with (i | i) | i <;> cases s
    all_goals first | exact i.elim | rfl
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change (u ∘ rvHead ∈ B ∧ v ∘ rvHead = (u ∘ rvHead) ∘ sel ∧ _) ↔
    (u ∘ rvHead ∈ B ∧ (∀ i, (v ∘ rvHead) i = ((u ∘ rvHead) ∘ sel) i) ∧ (fun s => a s ∘ old s) ∈ G)
  rw [eq]
  exact and_congr_right (fun _ => and_congr_left (fun _ => ⟨fun e i => congrFun e i,funext⟩))

theorem gluedRVGraph_finite_labels (sel : Fin t → Fin h)
    {B : Set (Fin h → X .rv)}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (finiteBase : ∀ q : Fin t → X .rv, {p ∈ B | p ∘ sel = q}.Finite)
    (finiteLocal : ∀ p ∈ B, ∀ w : SortedAssignment X V,
      {u | appendAssignments (appendAssignments (rvTupleAssignment p) u) w ∈ G}.Finite)
    (y : Fin (t+k) → X .rv) :
    {u | RVObject.labelGraphTuple u y ∈ gluedRVGraph sel B G}.Finite := by
  let b := y ∘ rvHead
  let w := rvTupleAssignment (y ∘ rvTail)
  let C (p : Fin h → X .rv) := {u : SortedAssignment X U |
      appendAssignments (appendAssignments (rvTupleAssignment p) u) w ∈ G}
  let parts (p : Fin h → X .rv) := (fun u : SortedAssignment X U => concatRV p (u .rv)) '' C p
  have f (p : Fin h → X .rv) (hp : p ∈ {p ∈ B | p ∘ sel = b}) : (parts p).Finite :=
    (finiteLocal p hp.1 w).image _
  apply ((finiteBase b).biUnion f).subset
  intro u hu
  let p := u ∘ rvHead
  let x := rvTupleAssignment (u ∘ rvTail)
  change p ∈ B ∧ b = p ∘ sel ∧ appendAssignments (appendAssignments (rvTupleAssignment p) x) w ∈ G at hu
  exact Set.mem_iUnion₂.2 ⟨p,⟨hu.1,hu.2.1.symm⟩,x,hu.2.2,concatRV_split u⟩

theorem gluedRVObject_exists (sel : Fin t → Fin h)
    {B : Set (Fin h → X .rv)} (defB : isRVSet M S B)
    {D : Set (SortedAssignment X (SumVariables P U))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (defD : SortedDefinableOver M S.carrier D) (defG : SortedDefinableOver M S.carrier G)
    (headNonzero : ∀ p ∈ B, ∀ i, p (sel i) ≠ M.funMap .rvZero (fun j => j.elim0))
    (finiteBase : ∀ q : Fin t → X .rv, {p ∈ B | p ∘ sel = q}.Finite)
    (valid : ∀ p ∈ B, ∃ bound, RelativeRVWitness D G (M.funMap .rvZero (fun j => j.elim0)) bound
      (rvTupleAssignment p)) :
    ∃ W : RVObject M S (t+k), ∃ ea : W.arity = h+m,
      (∀ x : Fin (h+m) → X .rv, x ∘ Fin.cast ea ∈ W.carrier ↔ x ∈ gluedRVTags B D) ∧
      ∀ x : W.carrier, RVObject.labelGraphTuple (x.val ∘ Fin.cast ea.symm) (W.label x) ∈ gluedRVGraph sel B G := by
  let A := gluedRVTags B D
  let H := gluedRVGraph sel B G
  have tot (u : Fin (h+m) → X .rv) : u ∈ A ↔ ∃ v, RVObject.labelGraphTuple u v ∈ H := by
    let p := u ∘ rvHead
    let x := rvTupleAssignment (u ∘ rvTail)
    constructor
    · rintro ⟨hp,hx⟩
      obtain ⟨_,wvalid⟩ := valid p hp
      obtain ⟨r,hr⟩ := (wvalid.1 x).1 hx
      refine ⟨concatRV (p ∘ sel) (r .rv),hp,?_⟩
      change (concatRV (p ∘ sel) (r .rv) ∘ rvHead = p ∘ sel) ∧
        appendAssignments (appendAssignments (rvTupleAssignment p) x)
          (rvTupleAssignment (concatRV (p ∘ sel) (r .rv) ∘ rvTail)) ∈ G
      rw [concatRV_head,concatRV_tail]
      refine ⟨rfl,?_⟩
      have e : rvTupleAssignment (r .rv) = r := by
        funext s i
        cases s
        · exact i.elim
        · rfl
      rwa [e]
    · rintro ⟨v,hp,_,hr⟩
      obtain ⟨_,wvalid⟩ := valid p hp
      exact ⟨hp,(wvalid.1 x).2 ⟨rvTupleAssignment (v ∘ rvTail),hr⟩⟩
  have func (u : Fin (h+m) → X .rv) (v w : Fin (t+k) → X .rv)
      (hv : RVObject.labelGraphTuple u v ∈ H) (hw : RVObject.labelGraphTuple u w ∈ H) : v = w := by
    obtain ⟨hp,headV,tailV⟩ := hv
    obtain ⟨_,headW,tailW⟩ := hw
    obtain ⟨_,wvalid⟩ := valid (u ∘ rvHead) hp
    have tails := congrFun (wvalid.2.1 _ _ _ tailV tailW) .rv
    change v ∘ rvHead = (u ∘ rvHead) ∘ sel at headV
    change w ∘ rvHead = (u ∘ rvHead) ∘ sel at headW
    change v ∘ rvTail = w ∘ rvTail at tails
    calc
      v = concatRV (v ∘ rvHead) (v ∘ rvTail) := (concatRV_split v).symm
      _ = concatRV (w ∘ rvHead) (w ∘ rvTail) := by rw [headV,headW,tails]
      _ = w := concatRV_split w
  have nz (u : Fin (h+m) → X .rv) (v : Fin (t+k) → X .rv)
      (hv : RVObject.labelGraphTuple u v ∈ H) (i : Fin (t+k)) : v i ≠ M.funMap .rvZero (fun j => j.elim0) := by
    obtain ⟨hp,headV,tailV⟩ := hv
    obtain ⟨_,wvalid⟩ := valid (u ∘ rvHead) hp
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i
    · have e : v (rvHead i) = u (rvHead (sel i)) := congrFun headV i
      change v (rvHead i) ≠ _
      rw [e]
      exact headNonzero _ hp i
    · exact wvalid.2.2.1 _ _ tailV i
  have finite := gluedRVGraph_finite_labels sel (G := G) finiteBase (fun p hp w => (valid p hp).choose_spec.finite_fiber w)
  let W := RVObject.ofLabelGraph A H (gluedRVTags_definable defB defD)
    (gluedRVGraph_definable sel defB defG) tot func nz finite
  refine ⟨W,rfl,?_,?_⟩
  · intro u
    change u ∈ A ↔ u ∈ A
    rfl
  · intro u
    change RVObject.labelGraphTuple u.val (RVObject.labelFromGraph A H tot u) ∈ H
    exact RVObject.labelFromGraph_mem A H tot u

end GeneralizedEuler.Section5
