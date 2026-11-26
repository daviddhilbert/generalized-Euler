module

public import Section5.RelativeLabelSchemes

/-! An RV object and lift isomorphism over an individual generated
base provide a witness scheme over the original base. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {P U : TCsort → Type}

theorem rvObject_uniform_label_bound {k : ℕ} (B : RVObject M S k)
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier (RVVariables (Fin k)))
      (BaseAssignments S.carrier (RVVariables (Fin k)))) :
    ∃ bound : ℕ, ∀ (x : Fin k → X .rv) (a : Fin (bound+1) → B.carrier),
      (∀ i, B.label (a i) = x) → ¬ Function.Injective a := by
  let R := RVVariables (Fin k)
  let T := RVVariables (Fin B.arity)
  let W := SumVariables R T
  let flip (s : TCsort) : RVVariables (Fin B.arity ⊕ Fin k) s → W s :=
    match s with
    | .vf => PEmpty.elim
    | .rv => Sum.elim Sum.inr Sum.inl
  let D := {w : SortedAssignment X W | ∃ b : B.carrier,
    b.val = w .rv ∘ Sum.inr ∧ B.label b = w .rv ∘ Sum.inl}
  have hd : SortedDefinableOver M S.carrier D := B.graph.pullback_relabel flip
  have univ : SortedDefinableOver M S.carrier (Set.univ : Set (SortedAssignment X R)) :=
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
  have fin (p : SortedAssignment X R) : {t | appendAssignments p t ∈ D}.Finite := by
    apply ((B.finiteFibers (p .rv)).image (fun b => rvTupleAssignment b.val)).subset
    rintro t ⟨b,hb,he⟩
    refine ⟨b,he,?_⟩
    funext s i
    cases s
    · exact i.elim
    · exact congrFun hb i
  obtain ⟨bound,hbound⟩ := uniform_finite_fiber_bound sat Set.univ univ D hd (fun p _ => fin p)
  refine ⟨bound,fun x a hx inj => ?_⟩
  let p : SortedAssignment X R := rvTupleAssignment x
  let f (i : Fin (bound+1)) : SortedAssignment X T := rvTupleAssignment (a i).val
  apply hbound p (Set.mem_univ _) f (fun i => ⟨a i,rfl,hx i⟩)
  intro i j eq
  exact inj (Subtype.ext (congrFun eq .rv))

theorem relativeRVLiftScheme_of_object {k : ℕ}
    (A : Set (SortedAssignment X (SumVariables P U))) (p : SortedAssignment X P)
    (zero : S.carrier .rv) (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (B : RVObject M (M.termGenerated (namedTuple S p)) k)
    (F : {u : SortedAssignment X U | appendAssignments p u ∈ A} ≃ ObjectLift.carrier B)
    (defF : DefinableRelation M (M.termGenerated (namedTuple S p)).carrier
      (fun a b => ∃ h : appendAssignments p a ∈ A, (F ⟨a,h⟩).val = b))
    (bound : ℕ) (fibers : ∀ (x : Fin k → X .rv) (a : Fin (bound+1) → B.carrier),
      (∀ i, B.label (a i) = x) → ¬ Function.Injective a) :
    ∃ i : RelativeRVLiftScheme M S P U, i.valid A zero p := by
  let W := ObjectLift.Vars B
  obtain ⟨D',G',hd',hg',dEq,enc⟩ := relative_rv_labels_of_object p B
  obtain ⟨J',hj',graph⟩ := definable_relation_fiber_as_scheme p _ defF
  let i : RelativeRVLiftScheme M S P U := ⟨B.arity,k,bound,D',G',J',hd',hg',hj'⟩
  refine ⟨i,?_,?_⟩
  · exact relativeRVWitness_of_labelRelation p B dEq enc zero.val hzero bound fibers
  · have image (b : SortedAssignment X W) :
        appendAssignments p b ∈ relativeRVLift (M := M) G' ↔ b ∈ ObjectLift.carrier B := by
      change appendAssignments (appendAssignments p (rvTupleAssignment (b .rv)))
          (rvTupleAssignment (M.rvMap ∘ b .vf)) ∈ G' ↔ _
      rw [enc]
      exact ⟨fun ⟨h,he⟩ => ⟨⟨_,h⟩,rfl,he⟩,fun ⟨⟨_,h⟩,rfl,he⟩ => ⟨h,he⟩⟩
    unfold FiberBijectionScheme
    simp only [i,graph,image]
    refine ⟨?_,?_,?_,?_⟩
    · exact fun a => ⟨fun ha => ⟨(F ⟨a,ha⟩).val,ha,rfl⟩,fun ⟨_,ha,_⟩ => ha⟩
    · intro b
      constructor
      · intro hb
        obtain ⟨a,ha⟩ := F.surjective ⟨b,hb⟩
        exact ⟨a.val,a.property,congrArg Subtype.val ha⟩
      · rintro ⟨a,ha,rfl⟩
        exact (F ⟨a,ha⟩).property
    · rintro a b c ⟨ha,hb⟩ ⟨_,hc⟩
      exact hb.symm.trans hc
    · rintro b a c ⟨ha,hb⟩ ⟨hc,he⟩
      exact congrArg Subtype.val (F.injective (Subtype.ext (hb.trans he.symm)))

theorem uniform_relative_rv_lifts_of_objects [Finite (U .vf)] [Finite (U .rv)]
    (sat : RealizesFinitelySatisfiableTypes M (WithBase S.carrier P) (BaseAssignments S.carrier P))
    (zero : S.carrier .rv) (hzero : zero.val = M.funMap .rvZero (fun i => i.elim0))
    (D : Set (SortedAssignment X P)) (hD : SortedDefinableOver M S.carrier D)
    (A : Set (SortedAssignment X (SumVariables P U))) (ha : SortedDefinableOver M S.carrier A)
    (satLocal : ∀ p ∈ D, ∀ k, let T := M.termGenerated (namedTuple S p)
      RealizesFinitelySatisfiableTypes M (WithBase T.carrier (RVVariables (Fin k)))
        (BaseAssignments T.carrier (RVVariables (Fin k))))
    (cover : ∀ p ∈ D, ∃ (k : ℕ) (B : RVObject M (M.termGenerated (namedTuple S p)) k)
      (F : {u : SortedAssignment X U | appendAssignments p u ∈ A} ≃ ObjectLift.carrier B),
      DefinableRelation M (M.termGenerated (namedTuple S p)).carrier
        (fun a b => ∃ h : appendAssignments p a ∈ A, (F ⟨a,h⟩).val = b)) :
    ∃ (C : Finset (RelativeRVLiftScheme M S P U)) (pieces : {i // i ∈ C} → Set (SortedAssignment X P)),
      (∀ i, SortedDefinableOver M S.carrier (pieces i)) ∧
      (∀ i p, p ∈ pieces i → i.val.valid A zero p) ∧
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧ (⋃ i, pieces i) = D := by
  apply uniform_relative_rv_lifts sat zero D hD A ha
  intro p hp
  obtain ⟨k,B,F,hF⟩ := cover p hp
  obtain ⟨bound,hbound⟩ := rvObject_uniform_label_bound B (satLocal p hp k)
  exact relativeRVLiftScheme_of_object A p zero hzero B F hF bound hbound

end GeneralizedEuler.Section5
