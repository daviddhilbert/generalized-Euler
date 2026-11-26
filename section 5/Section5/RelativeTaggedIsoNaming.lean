module

public import Section5.RelativeRVGraphNaming
public import Section5.GradedFamilyIsomorphism
import all Section4.RVTaggedEquivalence

/-! An equality of positive graded classes over a generated base
gives a valid matrix of named relative isomorphism schemes. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P : TCsort → Type}
  {I J : Type} [Fintype I] [Fintype J]

private theorem rv_cast_set_equiv {T : SortedSubstructure M} {m n : ℕ} (eq : m = n)
    {C : Set (Fin m → X .rv)} (defC : isRVSet M T C) :
    RVDefinablyEquivalent M T.carrier C {u | u ∘ Fin.cast eq ∈ C} := by
  subst n
  have same : {u : Fin m → X .rv | u ∘ Fin.cast rfl ∈ C} = C := by ext u; rfl
  rw [same]
  exact ⟨Equiv.refl _,definable_identity_label M T defC⟩

theorem relative_tagged_iso_scheme_of_class_eq
    (p : SortedAssignment X P)
    (A : I → RelativeRVTags M S P) (B : J → RelativeRVTags M S P)
    (U : ∀ i, RVObject M (M.termGenerated (namedTuple S p)) (A i).degree)
    (V : ∀ j, RVObject M (M.termGenerated (namedTuple S p)) (B j).degree)
    (arityU : ∀ i, (U i).arity = (A i).arity) (arityV : ∀ j, (V j).arity = (B j).arity)
    (matchU : ∀ i (u : SortedAssignment X (A i).Vars),
      appendAssignments p u ∈ (A i).tags ↔ u .rv ∘ Fin.cast (arityU i) ∈ (U i).carrier)
    (matchV : ∀ j (v : SortedAssignment X (B j).Vars),
      appendAssignments p v ∈ (B j).tags ↔ v .rv ∘ Fin.cast (arityV j) ∈ (V j).carrier)
    (eq : (∑ i, objectClass M (M.termGenerated (namedTuple S p)) ⟨(A i).degree,U i⟩) =
      ∑ j, objectClass M (M.termGenerated (namedTuple S p)) ⟨(B j).degree,V j⟩) :
    ∃ W : RelativeTaggedIsoScheme A B, W.valid p := by
  classical
  let T := M.termGenerated (namedTuple S p)
  let us (i : I) : GradedObject M T := ⟨(A i).degree,U i⟩
  let vs (j : J) : GradedObject M T := ⟨(B j).degree,V j⟩
  let F := taggedGradedFamily M T us
  let H := taggedGradedFamily M T vs
  obtain ⟨e,degree,graph⟩ := equal_graded_classes_tagged_iso M T us vs eq
  let left (i : I) (j : J) : Set (Fin (A i).arity → X .rv) :=
    {u | u ∘ Fin.cast (arityU i) ∈ sourceGraphCut F H e i j}
  let right (j : J) (i : I) : Set (Fin (B j).arity → X .rv) :=
    {v | v ∘ Fin.cast (arityV j) ∈ sourceGraphCut H F e.symm j i}
  have defLeft i j : isRVSet M T (left i j) :=
    isRVSet_precomp (Fin.cast (arityU i)) (sourceGraphCut_definable F H e i j (graph i j))
  have defRight j i : isRVSet M T (right j i) :=
    isRVSet_precomp (Fin.cast (arityV j)) (sourceGraphCut_definable H F e.symm j i (RVFamily.inverse_graph F H e graph j i))
  have nameLeft (i : I) (j : J) := definable_fiber_as_scheme p _ (defLeft i j)
  have nameRight (j : J) (i : I) := definable_fiber_as_scheme p _ (defRight j i)
  choose C defC matchC using nameLeft
  choose D defD matchD using nameRight
  have matrix (i : I) (j : J) :
      ∃ G : Set (SortedAssignment X (SumVariables (SumVariables P (A i).Vars) (B j).Vars)),
        SortedDefinableOver M S.carrier G ∧ FiberBijectionScheme (C i j) (D j i) G p := by
    apply relative_bijection_scheme_of_rv_equiv p (matchC i j) (matchD j i)
    have leftIso := rv_cast_set_equiv (arityU i) (sourceGraphCut_definable F H e i j (graph i j))
    have rightIso := rv_cast_set_equiv (arityV j) (sourceGraphCut_definable H F e.symm j i
      (RVFamily.inverse_graph F H e graph j i))
    let := (inferInstanceAs (Finite (Fin (U i).arity)) : Finite (F.Coord i))
    let := (inferInstanceAs (Finite (Fin (V j).arity)) : Finite (H.Coord j))
    exact leftIso.symm.trans ((sourceGraphCut_equivalent F H e i j (graph i j)).trans rightIso)
  choose G defG bij using matrix
  let W : RelativeTaggedIsoScheme A B := ⟨C,D,G,defC,defD,defG⟩
  refine ⟨W,?_,?_,bij,?_⟩
  · intro i
    obtain ⟨disj,cover⟩ := sourceGraphCut_partition F H e i
    refine ⟨fun u => ?_,fun j l ne u h => ?_⟩
    · refine (matchU i u).trans ?_
      change u .rv ∘ Fin.cast (arityU i) ∈ F.piece i ↔ ∃ j, appendAssignments p u ∈ C i j
      rw [← cover]
      exact Set.mem_iUnion.trans (exists_congr (fun j => (matchC i j u).symm))
    · exact Set.disjoint_left.1 (disj ne) ((matchC i j u).1 h.1) ((matchC i l u).1 h.2)
  · intro j
    obtain ⟨disj,cover⟩ := sourceGraphCut_partition H F e.symm j
    refine ⟨fun v => ?_,fun i l ne v h => ?_⟩
    · refine (matchV j v).trans ?_
      change v .rv ∘ Fin.cast (arityV j) ∈ H.piece j ↔ ∃ i, appendAssignments p v ∈ D j i
      rw [← cover]
      exact Set.mem_iUnion.trans (exists_congr (fun i => (matchD j i v).symm))
    · exact Set.disjoint_left.1 (disj ne) ((matchD j i v).1 h.1) ((matchD j l v).1 h.2)
  · intro i j ne u hu
    obtain ⟨x,_,hx⟩ := (matchC i j u).1 hu
    exact ne ((degree ⟨i,x⟩).symm.trans (congrArg (fun j => (B j).degree) hx))

end GeneralizedEuler.Section5
