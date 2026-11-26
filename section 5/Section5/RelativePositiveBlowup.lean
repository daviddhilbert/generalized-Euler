module

public import Section5.RelativeLabelDeletion
public import Section5.BlowupMultiplierDefinability
public import Section5.GradedBlowupLabels

/-! Append a nonzero multiplier and change only one active label
coordinate, retaining all original tags and the parameter tuple. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  {P : TCsort → Type} {m k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "X" => CanonicalSort O
local notation "U" => RVVariables (Fin m)
local notation "U⁺" => RVVariables (Fin (m+1))
local notation "V" => RVVariables (Fin (k+1))

@[expose] def retainOldRVTags (u : SortedAssignment X U⁺) : SortedAssignment X U
  | .vf => PEmpty.elim
  | .rv => u .rv ∘ Fin.castSucc

@[expose] def relativePositiveTags (D : Set (SortedAssignment X (SumVariables P U))) :
    Set (SortedAssignment X (SumVariables P U⁺)) :=
  {a | let u : SortedAssignment X U⁺ := fun s => a s ∘ Sum.inr
       appendAssignments (fun s => a s ∘ Sum.inl) (retainOldRVTags O u) ∈ D ∧
        unsignedValue O (u .rv (Fin.last m)) < 1 ∧ u .rv (Fin.last m) ≠ 0}

theorem relativePositiveTags_definable
    (hneg : rv O (-1) ∈ S.carrier .rv)
    {D : Set (SortedAssignment X (SumVariables P U))}
    (defD : SortedDefinableOver 𝓜 S.carrier D) :
    SortedDefinableOver 𝓜 S.carrier (relativePositiveTags O D) := by
  let old : (s : TCsort) → SumVariables P U s → SumVariables P U⁺ s
    | .vf => Sum.elim Sum.inl PEmpty.elim
    | .rv => Sum.map id Fin.castSucc
  let multiplier : (s : TCsort) → RVVariables (Fin 1) s → SumVariables P U⁺ s
    | .vf => PEmpty.elim
    | .rv => fun _ => .inr (Fin.last m)
  convert (defD.pullback_relabel old).inter
    ((nonzero_multipliers_definable O hO power S hneg).pullback_relabel multiplier) using 1
  ext a
  have eq : (fun s => a s ∘ old s) =
      appendAssignments (fun s => a s ∘ Sum.inl) (retainOldRVTags O (fun s => a s ∘ Sum.inr)) := by
    funext s i
    rcases i with i | i
    · cases s <;> rfl
    · cases s
      · exact i.elim
      · rfl
  change (_ ∧ _) ↔ (fun s => a s ∘ old s) ∈ D ∧ _
  rw [eq]
  rfl

@[expose] def relativeMultiplyAssignment (j : Fin (k+1)) (t : RV0 O)
    (v : SortedAssignment X V) : SortedAssignment X V :=
  rvTupleAssignment (Function.update (v .rv) j (t * v .rv j))

@[expose] def relativePositiveGraph (j : Fin (k+1))
    (D : Set (SortedAssignment X (SumVariables P U)))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))) :
    Set (SortedAssignment X (SumVariables (SumVariables P U⁺) V)) :=
  {a | let b : SortedAssignment X (SumVariables P U⁺) := fun s => a s ∘ Sum.inl
       let u : SortedAssignment X U⁺ := fun s => b s ∘ Sum.inr
       b ∈ relativePositiveTags O D ∧
        ∃ v : SortedAssignment X V,
          appendAssignments (appendAssignments (fun s => b s ∘ Sum.inl) (retainOldRVTags O u)) v ∈ G ∧
          relativeMultiplyAssignment O j (u .rv (Fin.last m)) v = (fun s => a s ∘ Sum.inr)}

theorem relativePositiveGraph_definable (j : Fin (k+1))
    (hneg : rv O (-1) ∈ S.carrier .rv)
    {D : Set (SortedAssignment X (SumVariables P U))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    (defD : SortedDefinableOver 𝓜 S.carrier D) (defG : SortedDefinableOver 𝓜 S.carrier G) :
    SortedDefinableOver 𝓜 S.carrier (relativePositiveGraph O j D G) := by
  let A := SumVariables (SumVariables P U⁺) V
  let B := SumVariables A V
  let take : (s : TCsort) → SumVariables (SumVariables P U) V s → B s
    | .vf => Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) PEmpty.elim) PEmpty.elim
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.map id Fin.castSucc) Sum.inr
  let T := WithBase S.carrier B
  let term (i : Fin (k+1)) : SortedTerm L E T .rv :=
    if i = j then rvMulTerm (.var (.inr (.inl (.inl (.inr (Fin.last m))))))
      (.var (.inr (.inr j))) else .var (.inr (.inr i))
  have coords := SortedDefinableOver.iInter (fun i : Fin (k+1) =>
    SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := B)
      .rv (.inl (.inr i)) (term i))
  have outer := (relativePositiveTags_definable O hneg defD).pullback_relabel
    (fun s => (Sum.inl : SumVariables P U⁺ s → A s))
  convert outer.inter (definable_project_mixed ((defG.pullback_relabel take).inter coords)) using 1
  ext a
  let p : SortedAssignment X P := fun s => a s ∘ Sum.inl ∘ Sum.inl
  let b : SortedAssignment X (SumVariables P U⁺) := fun s => a s ∘ Sum.inl
  let u : SortedAssignment X U⁺ := fun s => a s ∘ Sum.inl ∘ Sum.inr
  let w : SortedAssignment X V := fun s => a s ∘ Sum.inr
  change (b ∈ relativePositiveTags O D ∧ ∃ v, appendAssignments (appendAssignments p (retainOldRVTags O u)) v ∈ G ∧
      relativeMultiplyAssignment O j (u .rv (Fin.last m)) v = w) ↔ _
  have eq (v : SortedAssignment X V) :
      (fun s => appendAssignments a v s ∘ take s) = appendAssignments (appendAssignments p (retainOldRVTags O u)) v := by
    funext s i
    rcases i with (i | i) | i
    · cases s <;> rfl
    · cases s
      · exact i.elim
      · rfl
    · cases s
      · exact i.elim
      · rfl
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq,b]
  refine and_congr_right (fun _ => exists_congr (fun v => ?_))
  let val : (s : TCsort) → T s → X s := fun s => Sum.elim Subtype.val (appendAssignments a v s)
  change (appendAssignments (appendAssignments p (retainOldRVTags O u)) v ∈ G ∧
      relativeMultiplyAssignment O j (u .rv (Fin.last m)) v = w) ↔
    (fun s => appendAssignments a v s ∘ take s) ∈ G ∧ ∀ i, w .rv i = (term i).realize 𝓜 val
  rw [eq]
  refine and_congr_right (fun _ => ?_)
  have coord (i : Fin (k+1)) :
      (term i).realize 𝓜 val = (relativeMultiplyAssignment O j (u .rv (Fin.last m)) v) .rv i := by
    by_cases hi : i = j
    · subst i
      simp only [term,ite_true,realize_rvMulTerm O hO power,relativeMultiplyAssignment,rvTupleAssignment,
        Function.update_self]
      rfl
    · simp only [term,ite_eq_right hi,relativeMultiplyAssignment,rvTupleAssignment,Function.update_of_ne hi]
      rfl
  change relativeMultiplyAssignment O j (u .rv (Fin.last m)) v = w ↔
    ∀ i, w .rv i = (term i).realize 𝓜 val
  simp only [coord]
  constructor
  · intro e i
    exact congrFun (congrFun e.symm .rv) i
  · intro e
    funext s i
    cases s
    · exact i.elim
    · exact (e i).symm

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem relativePositiveGraph_iff (j : Fin (k+1))
    (D : Set (SortedAssignment X (SumVariables P U)))
    (G : Set (SortedAssignment X (SumVariables (SumVariables P U) V)))
    (p : SortedAssignment X P) (u : SortedAssignment X U⁺) (w : SortedAssignment X V) :
    appendAssignments (appendAssignments p u) w ∈ relativePositiveGraph O j D G ↔
      appendAssignments p u ∈ relativePositiveTags O D ∧
        ∃ v, appendAssignments (appendAssignments p (retainOldRVTags O u)) v ∈ G ∧
          relativeMultiplyAssignment O j (u .rv (Fin.last m)) v = w := Iff.rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem relativePositiveGraph_valid (j : Fin (k+1))
    {D : Set (SortedAssignment X (SumVariables P U))}
    {G : Set (SortedAssignment X (SumVariables (SumVariables P U) V))}
    {oldBound newBound : ℕ} {p : SortedAssignment X P}
    (old : RelativeRVWitness D G 0 oldBound p)
    (deleted : RelativeRVWitness D (relativeDeleteLabelGraph j G) 0 newBound p) :
    RelativeRVWitness (relativePositiveTags O D) (relativePositiveGraph O j D G) 0 newBound p := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u
    constructor
    · intro hu
      obtain ⟨v,hv⟩ := (old.1 (retainOldRVTags O u)).1 (show
        appendAssignments p (retainOldRVTags O u) ∈ D from hu.1)
      exact ⟨_,(relativePositiveGraph_iff O j D G p u _).2 ⟨hu,v,hv,rfl⟩⟩
    · rintro ⟨w,hw⟩
      exact ((relativePositiveGraph_iff O j D G p u w).1 hw).1
  · intro u w w' hw hw'
    obtain ⟨_,v,hv,eq⟩ := (relativePositiveGraph_iff O j D G p u w).1 hw
    obtain ⟨_,v',hv',eq'⟩ := (relativePositiveGraph_iff O j D G p u w').1 hw'
    rw [← eq,← eq',old.2.1 _ _ _ hv hv']
  · intro u w hw i
    obtain ⟨hu,v,hv,rfl⟩ := (relativePositiveGraph_iff O j D G p u w).1 hw
    exact blowupLabel_nonzero O j (fun v : SortedAssignment X V => v .rv) (v,u .rv (Fin.last m))
      (old.2.2.1 _ _ hv) hu.2.2 i
  · intro w a ha inj
    let b (i : Fin (newBound+1)) := retainOldRVTags O (a i)
    have witnesses (i : Fin (newBound+1)) := (relativePositiveGraph_iff O j D G p (a i) w).1 (ha i)
    choose v hv eq using fun i => (witnesses i).2
    have delete_eq (i : Fin (newBound+1)) : deleteRVAssignment j (v i) = deleteRVAssignment j w := by
      funext s l
      cases s
      · exact l.elim
      · have he := congrFun (congrFun (eq i) .rv) (j.succAbove l)
        change Function.update ((v i) .rv) j ((a i) .rv (Fin.last m) * (v i) .rv j) (j.succAbove l) =
          w .rv (j.succAbove l) at he
        rwa [Function.update_of_ne (Fin.succAbove_ne j l)] at he
    have inDeleted (i : Fin (newBound+1)) :
        appendAssignments (appendAssignments p (b i)) (deleteRVAssignment j w) ∈ relativeDeleteLabelGraph j G :=
      (relativeDeleteLabelGraph_iff j G p (b i) _).2 ⟨v i,hv i,delete_eq i⟩
    apply deleted.2.2.2 _ b inDeleted
    intro i l same
    apply inj
    have hvail : appendAssignments (appendAssignments p (b i)) (v l) ∈ G := same.symm ▸ hv l
    have vSame := old.2.1 (b i) _ _ (hv i) hvail
    have mulSame := (congrFun (congrFun (eq i) .rv) j).trans (congrFun (congrFun (eq l).symm .rv) j)
    change Function.update ((v i) .rv) j ((a i) .rv (Fin.last m) * (v i) .rv j) j =
      Function.update ((v l) .rv) j ((a l) .rv (Fin.last m) * (v l) .rv j) j at mulSame
    rw [Function.update_self,Function.update_self,← vSame] at mulSame
    have lastSame : (a i) .rv (Fin.last m) = (a l) .rv (Fin.last m) := by
      rw [mul_comm (G := RV0 O) ((a i) .rv (Fin.last m)),mul_comm (G := RV0 O) ((a l) .rv (Fin.last m))] at mulSame
      exact rv_mul_left_cancel O (old.2.2.1 _ _ (hv i) j) mulSame
    funext s c
    cases s
    · exact c.elim
    · refine Fin.lastCases lastSame (fun d => ?_) c
      exact congrFun (congrFun same .rv) d

end GeneralizedEuler.Section5
