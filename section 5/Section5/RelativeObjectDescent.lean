module

public import Section5.RelativeObjectFamilies
public import Section5.RelativeRVTests

/-! Assemble the finite tag and graph tests needed for descent of
named objects and graded isomorphism matrices. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder RelativeObjectFamily RelativeRVTest

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {P Q : TCsort → Type}
  {I J : Type} [Fintype I] [Fintype J]

namespace RelativeRVTest

@[expose] def ofFamily {I₀ : Type*} [Fintype I₀]
    (tests : I₀ → List (RelativeRVTest M S P)) : List (RelativeRVTest M S P) :=
  (Finset.univ : Finset I₀).toList.flatMap tests

theorem agree_family {I₀ : Type*} [Fintype I₀] (tests : I₀ → List (RelativeRVTest M S P))
    {p p' : SortedAssignment X P} (agree : Agree (ofFamily tests) p p') (i : I₀) :
    Agree (tests i) p p' :=
  fun t ht => agree t (List.mem_flatMap.2 ⟨i,Finset.mem_toList.2 (Finset.mem_univ _),ht⟩)

end RelativeRVTest

namespace RelativeRVObjectScheme

@[expose] def tests (A : RelativeRVObjectScheme M S P) : List (RelativeRVTest M S P) :=
  [ofSet A.data.definable,ofGraph A.definable]

theorem descend_valid_of_tests [Finite (P .vf)] [Finite (P .rv)]
    (A : RelativeRVObjectScheme M S P)
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) {p : SortedAssignment X P} {q : SortedAssignment X Q}
    (hp : H p q) (agree : ∀ p', H p' q → Agree A.tests p p')
    (zero : S.carrier .rv) (v : A.valid zero p) : (A.descend defH).valid zero q :=
  A.descend_valid zero defH hp
    (fun p' h' => agree p' h' (ofSet A.data.definable) (by simp [tests]))
    (fun p' h' => same_ofGraph A.definable (agree p' h' (ofGraph A.definable) (by simp [tests]))) v

end RelativeRVObjectScheme

namespace RelativeObjectFamily

@[expose] def tests (A : RelativeObjectFamily M S P I) : List (RelativeRVTest M S P) :=
  ofFamily (fun i => (A i).tests)

theorem descend_valid_of_tests [Finite (P .vf)] [Finite (P .rv)]
    (A : RelativeObjectFamily M S P I)
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) {p : SortedAssignment X P} {q : SortedAssignment X Q}
    (hp : H p q) (agree : ∀ p', H p' q → Agree (tests A) p p')
    (zero : S.carrier .rv) (v : Valid A zero p) :
    Valid (fun i => (A i).descend defH) zero q :=
  fun i => (A i).descend_valid_of_tests defH hp
    (fun p' h' => agree_family _ (agree p' h') i) zero (v i)

end RelativeObjectFamily

namespace RelativeTaggedIsoScheme

variable {A : I → RelativeRVTags M S P} {B : J → RelativeRVTags M S P}

@[expose] def tests (W : RelativeTaggedIsoScheme A B) : List (RelativeRVTest M S P) :=
  ofFamily (fun i => [ofSet (A i).definable]) ++
    ofFamily (fun j => [ofSet (B j).definable]) ++
    ofFamily (fun ij : I × J => [ofSet (W.sourceDefinable ij.1 ij.2),
      ofSet (W.targetDefinable ij.2 ij.1),ofGraph (W.graphDefinable ij.1 ij.2)])

theorem descend_valid_of_tests [Finite (P .vf)] [Finite (P .rv)]
    (W : RelativeTaggedIsoScheme A B)
    {H : SortedAssignment X P → SortedAssignment X Q → Prop}
    (defH : DefinableRelation M S.carrier H) {p : SortedAssignment X P} {q : SortedAssignment X Q}
    (hp : H p q) (agree : ∀ p', H p' q → Agree W.tests p p')
    (v : W.valid p) : (W.descend defH).valid q := by
  have first p' h' := (agree_append.1 (agree p' h')).1
  have second p' h' := (agree_append.1 (agree p' h')).2
  have tagsA p' h' := (agree_append.1 (first p' h')).1
  have tagsB p' h' := (agree_append.1 (first p' h')).2
  have rect p' h' i j := agree_family _ (second p' h') (i,j)
  apply W.descend_valid defH hp _ _ _ _ _ v
  · exact fun i p' h' => agree_family _ (tagsA p' h') i (ofSet (A i).definable) (by simp)
  · exact fun j p' h' => agree_family _ (tagsB p' h') j (ofSet (B j).definable) (by simp)
  · exact fun i j p' h' => rect p' h' i j (ofSet (W.sourceDefinable i j)) (by simp)
  · exact fun j i p' h' => rect p' h' i j (ofSet (W.targetDefinable j i)) (by simp)
  · exact fun i j p' h' => same_ofGraph (W.graphDefinable i j)
      (rect p' h' i j (ofGraph (W.graphDefinable i j)) (by simp))

end RelativeTaggedIsoScheme

end GeneralizedEuler.Section5
