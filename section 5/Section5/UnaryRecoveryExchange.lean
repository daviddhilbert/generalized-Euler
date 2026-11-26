module

public import Section5.UnaryRecoveryPartition
public import Section2.RecoveredValuedField

/-! Field exchange gives the term tuple for the recovered coordinate.
The closure hypothesis is the conclusion of the RV-to-VF point theorem. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type}

set_option linter.style.haveILetI false in
theorem output_recovery_terms_of_exchange (i : Fin n)
    (a : SortedAssignment X (MixedVariables n I)) (b : SortedAssignment X (MixedVariables n J))
    (exchange : letI := valuedStructureOfSorted M ∅
      ∀ (D : Set (X .vf)) (x y : X .vf),
        y ∈ Substructure.closure (convexLanguage L) (insert x D) →
        y ∉ Substructure.closure (convexLanguage L) D →
        x ∈ Substructure.closure (convexLanguage L) (insert y D))
    (output : letI := valuedStructureOfSorted M ∅
      ∀ k, b .vf k ∈ Substructure.closure (convexLanguage L) (S.carrier .vf ∪ Set.range (a .vf))) :
    ∃ (j : Fin n) (T : FieldTermTuple M S (MixedVariables n Empty) n),
      (realizeFieldTuple T (recoveryInput i j a b)) .vf = b .vf := by
  classical
  letI := valuedStructureOfSorted M ∅
  let C := Substructure.closure (convexLanguage L) (M := X .vf)
  let kept := S.carrier .vf ∪ {x | ∃ k : Fin n, k ≠ i ∧ a .vf k = x}
  have orig : S.carrier .vf ∪ Set.range (a .vf) ⊆ insert (a .vf i) kept := by
    rintro x (hx | ⟨k,rfl⟩)
    · exact Set.mem_insert_of_mem _ (Or.inl hx)
    · by_cases hi : k = i
      · subst k
        exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Or.inr ⟨k,hi,rfl⟩)
  have found : ∃ j : Fin n, ∀ k, b .vf k ∈ C (insert (b .vf j) kept) := by
    by_cases all : ∀ k, b .vf k ∈ C kept
    · exact ⟨i,fun k => Substructure.closure_mono (Set.subset_insert _ _) (all k)⟩
    · obtain ⟨j,hj⟩ := not_forall.mp all
      let T := C (insert (b .vf j) kept)
      have hJ : b .vf j ∈ C (insert (a .vf i) kept) := Substructure.closure_mono orig (output j)
      have hA : a .vf i ∈ T := exchange kept (a .vf i) (b .vf j) hJ hj
      have sub : insert (a .vf i) kept ⊆ (T : Set (X .vf)) := by
        intro x hx
        rcases Set.mem_insert_iff.1 hx with rfl | h
        · exact hA
        · exact Substructure.subset_closure (Set.mem_insert_of_mem _ h)
      exact ⟨j,fun k => (Substructure.closure_le.2 sub) (Substructure.closure_mono orig (output k))⟩
  obtain ⟨j,hj⟩ := found
  let p := recoveryInput i j a b
  let Names := WithBase S.carrier (MixedVariables n Empty)
  let values : ∀ s, Names s → X s := fun s => Sum.elim Subtype.val (p s)
  have sub : insert (b .vf j) kept ⊆ Set.range (values .vf) := by
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | h
    · exact ⟨.inr i,Function.update_self i _ _⟩
    · rcases h with h | ⟨k,hk,rfl⟩
      · exact ⟨.inl ⟨x,h⟩,rfl⟩
      · exact ⟨.inr k,Function.update_of_ne hk _ _⟩
  have terms (k : Fin n) : ∃ t : (convexLanguage L).Term (Names .vf),
      t.realize (values .vf) = b .vf k := by
    have mem := Substructure.closure_mono sub (hj k)
    obtain ⟨t,ht⟩ := Substructure.mem_closure_iff_exists_term.mp mem
    let pick (x : Set.range (values .vf)) := x.property.choose
    refine ⟨t.relabel pick,?_⟩
    rwa [Term.realize_relabel,show values .vf ∘ pick = Subtype.val from funext fun x => x.property.choose_spec]
  choose term eq using terms
  refine ⟨j,fun k => liftValuedTerm SortedTerm.var (term k),?_⟩
  funext k
  change (liftValuedTerm SortedTerm.var (term k)).realize M values = b .vf k
  rw [realize_liftValuedTerm M (∅ : Set (X .vf))]
  exact eq k

theorem output_field_closure_of_immediate_movers
    (A : Set (SortedAssignment X (MixedVariables n I)))
    (B : Set (SortedAssignment X (MixedVariables n J))) (f : A ≃ B)
    (defF : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ A, (f ⟨a,ha⟩).val = b))
    (move : letI := valuedStructureOfSorted M ∅
      ∀ (a : A) (y : X .vf),
        y ∉ Substructure.closure (convexLanguage L) (S.carrier .vf ∪ Set.range (a.val .vf)) →
        ∃ e : SortedIsomorphism M M, e.toEmbedding .vf y ≠ y ∧
          (∀ x ∈ S.carrier .vf ∪ Set.range (a.val .vf), e.toEmbedding .vf x = x) ∧
          ∀ t : X .rv, e.toEmbedding .rv t = t) :
    letI := valuedStructureOfSorted M ∅
    ∀ (a : A) (k : Fin n), (f a).val .vf k ∈
      Substructure.closure (convexLanguage L) (S.carrier .vf ∪ Set.range (a.val .vf)) := by
  intro a k
  by_contra outside
  obtain ⟨e,neq,hvf,hrv⟩ := move a _ outside
  obtain ⟨φ,hφ⟩ := defF
  let w := appendAssignments a.val (f a).val
  let b := e.toSortedEmbedding.mapAssignment (f a).val
  let W := SumVariables (MixedVariables n I) (MixedVariables n J)
  let named (x : SortedAssignment X W) (s : TCsort) : WithBase S.carrier W s → X s :=
    Sum.elim Subtype.val (x s)
  have old : ∃ ha : a.val ∈ A, (f ⟨a.val,ha⟩).val = (f a).val := ⟨a.property,rfl⟩
  have holds := (hφ w).1 old
  have assignment : e.toSortedEmbedding.mapAssignment (named w) = named (appendAssignments a.val b) := by
    funext s k
    simp only [SortedEmbedding.mapAssignment_apply]
    rcases k with c | (i | j)
    · cases s
      · exact hvf _ (Or.inl c.property)
      · exact hrv _
    · cases s
      · exact hvf _ (Or.inr (Set.mem_range_self i))
      · exact hrv _
    · change e.toEmbedding s ((f a).val s j) = e.toSortedEmbedding.mapAssignment (f a).val s j
      rw [SortedEmbedding.mapAssignment_apply]
  have moved := (e.realize_iff φ (named w)).2 holds
  rw [assignment] at moved
  obtain ⟨_,eq⟩ : ∃ ha : a.val ∈ A, (f ⟨a.val,ha⟩).val = b :=
    (hφ (appendAssignments a.val b)).2 moved
  apply neq
  simpa only [b,SortedEmbedding.mapAssignment_apply] using (congrFun (congrFun eq.symm .vf) k)

end GeneralizedEuler.Section5
