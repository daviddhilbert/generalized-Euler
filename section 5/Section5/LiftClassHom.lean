module

public import Section5.LiftFieldObjects
public import Section5.ObjectLiftRestrictions
import all Section4.Objects
import all Section4.Scissors

/-! Descend the lifting construction to positive scissor classes using
the fixed-base lifting of RV isomorphisms. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  [TopologicalSpace (X .vf)]

/-- Corollary 5.13 supplies this compatibility for every degree. -/
abbrev LiftsRVIsomorphisms (M : SortedStructure L E X) (S : SortedSubstructure M) :=
  ∀ {k} (U V : RVObject M S k), RVDefinablyEquivalent M S.carrier U.carrier V.carrier →
    MixedDefinablyEquivalent M S (ObjectLift.carrier U) (ObjectLift.carrier V)

omit [TopologicalSpace (X .vf)] in
theorem lift_restrictTags_carrier {k : ℕ} (U : RVObject M S k)
    {D : Set (Fin U.arity → X .rv)} (sub : D ⊆ U.carrier) (defD : isRVSet M S D) :
    ObjectLift.carrier (ObjectLift.restrictTags U sub defD) =
      {a : SortedAssignment X (ObjectLift.Vars U) | a ∈ ObjectLift.carrier U ∧ a .rv ∈ D} := by
  ext a
  constructor
  · rintro ⟨u,hu,hl⟩
    exact ⟨⟨⟨u.val,sub u.property⟩,hu,hl⟩,hu ▸ u.property⟩
  · rintro ⟨⟨u,hu,hl⟩,hd⟩
    exact ⟨⟨u.val,hu.symm ▸ hd⟩,hu,hl⟩

private theorem lift_scissors_respected
    (liftIso : LiftsRVIsomorphisms M S)
    (a b : RVExpression M S) (h : RVRelation M S a b) :
    MvPolynomial.eval₂ (Nat.castRingHom (VFSemiring M S)) liftObjectClass a =
      MvPolynomial.eval₂ (Nat.castRingHom (VFSemiring M S)) liftObjectClass b := by
  cases h with
  | iso U V e =>
    simp only [MvPolynomial.eval₂_X]
    exact fieldClass_of_iso M S (A := ⟨_,liftFieldObject U⟩) (B := ⟨_,liftFieldObject V⟩) (liftIso U V e)
  | zero U empty =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_zero]
    apply field_scissors_sound M S
    apply VFRelation.zero
    apply Set.eq_empty_iff_forall_notMem.2
    rintro x ⟨u,_,_⟩
    exact Set.eq_empty_iff_forall_notMem.1 empty _ u.property
  | one U h =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_one]
    apply field_scissors_sound M S
    apply VFRelation.one
    obtain ⟨u,hu⟩ := h
    let x : SortedAssignment X (ObjectLift.Vars U)
      | .vf => Fin.elim0
      | .rv => u
    have ok : u ∈ U.carrier := hu.symm ▸ Set.mem_singleton _
    refine ⟨x,?_⟩
    ext a
    change a ∈ ObjectLift.carrier U ↔ a ∈ ({x} : Set _)
    constructor
    · rintro ⟨t,ht,_⟩
      apply Set.mem_singleton_iff.2
      have eq : t.val = u := Set.mem_singleton_iff.1 (hu ▸ t.property)
      funext s i
      cases s with
      | vf => exact i.elim0
      | rv => exact congrFun (ht.symm.trans eq) i
    · intro ha
      have eq : a = x := ha
      subst a
      exact ⟨⟨u,ok⟩,rfl,funext fun i => i.elim0⟩
  | cut U V W D E dDef eDef disj cover equD equE =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_add]
    unfold liftObjectClass fieldClass
    rw [← map_add]
    apply field_scissors_sound M S
    have subD : D ⊆ U.carrier := cover ▸ Set.subset_union_left
    have subE : E ⊆ U.carrier := cover ▸ Set.subset_union_right
    let U₁ := ObjectLift.restrictTags U subD dDef
    let U₂ := ObjectLift.restrictTags U subE eDef
    have hd := lift_restrictTags_carrier U subD dDef
    have he := lift_restrictTags_carrier U subE eDef
    apply VFRelation.cut _ _ _ (ObjectLift.carrier U₁) (ObjectLift.carrier U₂)
      (ObjectLift.definable U₁) (ObjectLift.definable U₂)
    · rw [hd,he]
      exact Set.disjoint_left.2 fun _ hx hy => Set.disjoint_left.1 disj hx.2 hy.2
    · rw [hd,he]
      apply Set.Subset.antisymm
      · exact Set.union_subset (fun _ h => h.1) (fun _ h => h.1)
      · intro a ha
        have old : a .rv ∈ U.carrier := by
          obtain ⟨u,hu,_⟩ := ha
          exact hu ▸ u.property
        have cut : a .rv ∈ D ∪ E := cover.symm ▸ old
        rcases cut with hh | hh
        · exact Or.inl ⟨ha,hh⟩
        · exact Or.inr ⟨ha,hh⟩
    · exact liftIso U₁ V equD
    · exact liftIso U₂ W equE
  | prod U V W e =>
    simp only [MvPolynomial.eval₂_X,MvPolynomial.eval₂_mul]
    let P := RVObject.cartesianProduct U V
    have he : RVDefinablyEquivalent M S.carrier (productSet U.carrier V.carrier) P.carrier :=
      rv_reindex_equivalent M S finSumFinEquiv.symm _ (rv_product_definable U.definable V.definable)
    have h := RVDefinablyEquivalent.trans (RVDefinablyEquivalent.symm e) he
    exact (fieldClass_of_iso M S (A := ⟨_,liftFieldObject W⟩) (B := ⟨_,liftFieldObject P⟩)
      (liftIso W P h)).trans (lift_cartesianProduct_class U V)

def liftClassHom (liftIso : LiftsRVIsomorphisms M S) : RVSemiring M S →+* VFSemiring M S :=
  descendWeights M S liftObjectClass (lift_scissors_respected liftIso)

theorem liftClassHom_class (liftIso : LiftsRVIsomorphisms M S) (U : GradedObject M S) :
    liftClassHom liftIso (objectClass M S U) = liftObjectClass U :=
  descendWeights_class M S liftObjectClass _ U

end GeneralizedEuler.Section5
