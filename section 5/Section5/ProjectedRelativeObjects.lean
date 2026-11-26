module

public import Section5.RelativeRVObjectSchemes
public import Section5.DefinableFiberBounds

/-! A definable relative tag carrier and a finite-to-one coordinate
projection give a named RV object scheme with a uniform bound. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type} {a k : ℕ}

local notation "U" => RVVariables (Fin a)
local notation "V" => RVVariables (Fin k)

@[expose] def relativeProjectionGraph (D : Set (SortedAssignment X (SumVariables P U)))
    (sel : Fin k → Fin a) :
    Set (SortedAssignment X (SumVariables (SumVariables P U) V)) :=
  {r | (fun s => r s ∘ Sum.inl) ∈ D ∧ r .rv ∘ Sum.inr = r .rv ∘ Sum.inl ∘ Sum.inr ∘ sel}

theorem relativeProjectionGraph_definable
    {D : Set (SortedAssignment X (SumVariables P U))} (defD : SortedDefinableOver M S.carrier D)
    (sel : Fin k → Fin a) : SortedDefinableOver M S.carrier (relativeProjectionGraph D sel) := by
  let W := SumVariables (SumVariables P U) V
  let left (s : TCsort) : SumVariables P U s → W s := Sum.inl
  have eqs := SortedDefinableOver.iInter (fun j : Fin k => SortedDefinableOver.coordinate_eq
    (M := M) (A := S.carrier) (Var := W) .rv (.inr j) (.inl (.inr (sel j))))
  convert (defD.pullback_relabel left).inter eqs using 1
  ext r
  simp only [relativeProjectionGraph,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  exact and_congr_right (fun _ => ⟨congrFun,funext⟩)

theorem relativeProjectionGraph_iff
    (D : Set (SortedAssignment X (SumVariables P U))) (sel : Fin k → Fin a)
    (p : SortedAssignment X P) (u : SortedAssignment X U) (v : SortedAssignment X V) :
    appendAssignments (appendAssignments p u) v ∈ relativeProjectionGraph D sel ↔
      appendAssignments p u ∈ D ∧ v .rv = u .rv ∘ sel := by
  have e : (fun s => appendAssignments (appendAssignments p u) v s ∘ Sum.inl) = appendAssignments p u := by
    funext s i
    rfl
  unfold relativeProjectionGraph
  simp only [Set.mem_ofPred_eq,e]
  rfl

@[expose] def RelativeRVObjectScheme.ofProjection {D : Set (SortedAssignment X (SumVariables P U))}
    (defD : SortedDefinableOver M S.carrier D) (sel : Fin k → Fin a) (bound : ℕ) :
    RelativeRVObjectScheme M S P :=
  ⟨⟨k,a,D,defD⟩,relativeProjectionGraph D sel,relativeProjectionGraph_definable defD sel,bound⟩

theorem relative_projection_scheme_valid
    {D : Set (SortedAssignment X (SumVariables P U))} (defD : SortedDefinableOver M S.carrier D)
    (sel : Fin k → Fin a) (zero : S.carrier .rv)
    (nz : ∀ p u, appendAssignments p u ∈ D → ∀ j, u .rv (sel j) ≠ zero.val)
    (finite : ∀ (p : SortedAssignment X P) (v : SortedAssignment X V),
      {u | appendAssignments p u ∈ D ∧ v .rv = u .rv ∘ sel}.Finite)
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (SumVariables P V))
      (BaseAssignments S.carrier (SumVariables P V))) :
    ∃ bound, ∀ p, (RelativeRVObjectScheme.ofProjection defD sel bound).valid zero p := by
  let graph := relativeProjectionGraph D sel
  let W := SumVariables (SumVariables P V) U
  let swap (s : TCsort) : SumVariables (SumVariables P U) V s → W s
    | .inl (.inl p) => .inl (.inl p)
    | .inl (.inr u) => .inr u
    | .inr v => .inl (.inr v)
  let D' : Set (SortedAssignment X W) := {r | (fun s => r s ∘ swap s) ∈ graph}
  have defD' : SortedDefinableOver M S.carrier D' := (relativeProjectionGraph_definable defD sel).pullback_relabel swap
  have test (p : SortedAssignment X P) (v : SortedAssignment X V) (u : SortedAssignment X U) :
      appendAssignments (appendAssignments p v) u ∈ D' ↔ appendAssignments p u ∈ D ∧ v .rv = u .rv ∘ sel := by
    have e : (fun s => appendAssignments (appendAssignments p v) u s ∘ swap s) =
        appendAssignments (appendAssignments p u) v := by
      funext s i
      rcases i with (i | i) | i <;> rfl
    change (fun s => appendAssignments (appendAssignments p v) u s ∘ swap s) ∈ graph ↔ _
    rw [e]
    exact relativeProjectionGraph_iff D sel p u v
  let all : Set (SortedAssignment X (SumVariables P V)) := Set.univ
  have defAll : SortedDefinableOver M S.carrier all :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  have finite' (b : SortedAssignment X (SumVariables P V)) (_ : b ∈ all) :
      {u | appendAssignments b u ∈ D'}.Finite := by
    let p : SortedAssignment X P := fun s => b s ∘ Sum.inl
    let v : SortedAssignment X V := fun s => b s ∘ Sum.inr
    have eq : appendAssignments p v = b := by
      funext s i
      cases i <;> rfl
    apply (finite p v).subset
    intro u hu
    apply (test p v u).1
    exact eq.symm ▸ hu
  obtain ⟨bound,hbound⟩ := uniform_finite_fiber_bound sat all defAll D' defD' finite'
  refine ⟨bound,fun p => ?_⟩
  change RelativeRVWitness D (relativeProjectionGraph D sel) zero.val bound p
  simp only [RelativeRVWitness,relativeProjectionGraph_iff]
  refine ⟨?_,?_,?_,?_⟩
  · intro u
    exact ⟨fun hu => ⟨rvTupleAssignment (u .rv ∘ sel),hu,rfl⟩,fun ⟨_,h,_⟩ => h⟩
  · rintro u v w ⟨_,hv⟩ ⟨_,hw⟩
    funext s i
    cases s
    · exact i.elim
    · exact congrFun (hv.trans hw.symm) i
  · rintro u v ⟨hu,eq⟩ i
    rw [eq]
    exact nz p u hu i
  · intro v u hu
    exact hbound (appendAssignments p v) (Set.mem_univ _) u (fun i => (test p v (u i)).2 (hu i))

end GeneralizedEuler.Section5
