module

public import Section5.ObjectLiftPartitions

/-! Corollary 5.13 via simultaneous finite-to-one label partitions. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.ObjectLift

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}

theorem structureLabels_nonzero (U : RVObject M S k) :
    ∀ a ∈ structureLabels U, ∀ j, a .rv j ≠ M.funMap .rvZero (fun i => i.elim0) := by
  rintro _ ⟨u,rfl⟩ j
  exact U.nonzero u j

/-- Partition both finite-to-one label maps and intersect the partitions
along the given isomorphism. On each pair the labels are injective, so the
lift on RV sets applies. -/
theorem definable_lift_of_rv_object_iso (U V : RVObject M S k) (e : U.carrier ≃ V.carrier)
    (eDef : SortedDefinableOver M S.carrier (rvGraph (fun a => (e a).val)))
    (ltU : (Fin U.arity → X .rv) → (Fin U.arity → X .rv) → Prop)
    (ltV : (Fin V.arity → X .rv) → (Fin V.arity → X .rv) → Prop)
    (transU : ∀ {a b c}, ltU a b → ltU b c → ltU a c)
    (transV : ∀ {a b c}, ltV a b → ltV b c → ltV a c)
    (irreflU : ∀ a, ¬ ltU a a) (irreflV : ∀ a, ¬ ltV a a)
    (totalU : ∀ a b, a ≠ b → ltU a b ∨ ltU b a)
    (totalV : ∀ a b, a ≠ b → ltV a b ∨ ltV b a)
    (defU : isRVSet M S {t : Fin U.arity ⊕ Fin U.arity → X .rv | ltU (t ∘ Sum.inr) (t ∘ Sum.inl)})
    (defV : isRVSet M S {t : Fin V.arity ⊕ Fin V.arity → X .rv | ltV (t ∘ Sum.inr) (t ∘ Sum.inl)})
    (sat : ∀ D : ℕ → Set (Fin k → X .rv), (∀ i, isRVSet M S (D i)) → Antitone D →
      (∀ i, (D i).Nonempty) → ∃ y, ∀ i, y ∈ D i)
    (liftSets : ∀ (A B : Set (labelAssignment k X)) (g : A ≃ B),
      SortedDefinableOver M S.carrier A → SortedDefinableOver M S.carrier B →
      DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ A, (g ⟨a,ha⟩).val = b) →
      (∀ a ∈ A, ∀ j, a .rv j ≠ M.funMap .rvZero (fun i => i.elim0)) →
      (∀ b ∈ B, ∀ j, b .rv j ≠ M.funMap .rvZero (fun i => i.elim0)) →
      HasDefinableFieldLift S g) :
    HasDefinableObjectLift U V e := by
  obtain ⟨N,disjU,coverU⟩ := U.tag_partition ltU sat
  obtain ⟨J,disjV,coverV⟩ := V.tag_partition ltV sat
  let A (ij : Fin N × Fin J) :=
    U.tagPiece ltU ij.1.val ∩ tagPreimage e (V.tagPiece ltV ij.2.val)
  have sub (ij : Fin N × Fin J) : A ij ⊆ U.carrier := fun _ h => h.1.1
  have hA (ij : Fin N × Fin J) : isRVSet M S (A ij) :=
    isRVSet_inter (U.tagPiece_definable ltU defU ij.1.val)
      (tagPreimage_definable e eDef (V.tagPiece_definable ltV defV ij.2.val))
  have disj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j ne
    refine Set.disjoint_left.2 ?_
    rintro a ⟨hu,ha,hv⟩ ⟨hu',_,hv'⟩
    by_cases he : i.1 = j.1
    · exact Set.disjoint_left.1 (disjV (fun he' => ne (Prod.ext he he'))) hv hv'
    · exact Set.disjoint_left.1 (disjU he) hu hu'
  have hCover (a : U.carrier) : ∃ ij, a.val ∈ A ij := by
    have hua : a.val ∈ ⋃ i : Fin N, U.tagPiece ltU i.val := by rw [coverU]; exact a.property
    have hva : (e a).val ∈ ⋃ j : Fin J, V.tagPiece ltV j.val := by rw [coverV]; exact (e a).property
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hua
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hva
    exact ⟨(i,j),hi,a.property,hj⟩
  apply definable_lift_of_tag_partition e eDef A sub hA disj hCover
  intro ij
  let U' := sourceRestriction (sub ij) (hA ij)
  let V' := targetRestriction e eDef (hA ij)
  let f := restrictIso e eDef (sub ij) (hA ij)
  have injU : Function.Injective U'.label := by
    intro a b h
    let a' : U.tagPiece ltU ij.1.val := ⟨a.val,a.property.1⟩
    let b' : U.tagPiece ltU ij.1.val := ⟨b.val,b.property.1⟩
    have eq := U.tagPiece_injective ltU transU irreflU totalU ij.1.val (a₁ := a') (a₂ := b') h
    exact Subtype.ext (congrArg (fun z : U.tagPiece ltU ij.1.val => z.val) eq)
  have vSub : tagImage e (A ij) ⊆ V.tagPiece ltV ij.2.val := by
    rintro _ ⟨a,⟨_,_,he⟩,rfl⟩
    exact he
  have injV : Function.Injective V'.label := by
    intro a b h
    let a' : V.tagPiece ltV ij.2.val := ⟨a.val,vSub a.property⟩
    let b' : V.tagPiece ltV ij.2.val := ⟨b.val,vSub b.property⟩
    have eq := V.tagPiece_injective ltV transV irreflV totalV ij.2.val (a₁ := a') (a₂ := b') h
    exact Subtype.ext (congrArg (fun z : V.tagPiece ltV ij.2.val => z.val) eq)
  exact definable_lift_of_injective_labels U' V' f (restrictIso_definable e eDef (sub ij) (hA ij)) injU injV
    (fun g hGraph => liftSets _ _ g (structureLabels_definable U') (structureLabels_definable V') hGraph
      (structureLabels_nonzero U') (structureLabels_nonzero V'))

end GeneralizedEuler.Section5.ObjectLift
