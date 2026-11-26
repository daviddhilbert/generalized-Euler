module

public import Section5.GradedRVProducts
public import Section5.MixedRelabeling
public import Section5.RVObjectLifts
import all Section2.Dimension

/-! The lift of a graded RV object is a filtered VF object. Products
of lifts agree with the lift of the Cartesian product of RV objects. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}

theorem ambient_vf_dimension_bound [TopologicalSpace (X .vf)] {n : ℕ} {R : Type*}
    (D : Set ((Fin n → X .vf) × R)) : vfDimension D ≤ n := by
  classical
  unfold vfDimension
  apply Finset.sup_le
  intro i hi
  exact Nat.le_of_lt_succ (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)

variable [TopologicalSpace (X .vf)] {k l : ℕ} (U : RVObject M S k) (V : RVObject M S l)

@[expose] def liftFieldObject : FieldObject M S k where
  vfArity := k
  rvArity := U.arity
  carrier := ObjectLift.carrier U
  definable := ObjectLift.definable U
  dimension := ambient_vf_dimension_bound _
  finiteFibers a := by
    let D := {x : ObjectLift.carrier U | x.val .vf = a}
    have hf : (fun x : ObjectLift.carrier U => x.val .rv) '' D =
        {r | (a,r) ∈ mixedTuple '' ObjectLift.carrier U} := by
      ext r
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨x.val,x.property,Prod.ext hx rfl⟩
      · rintro ⟨x,hx,he⟩
        exact ⟨⟨x,hx⟩,congrArg Prod.fst he,congrArg Prod.snd he⟩
    rw [← hf]
    exact (ObjectLift.finite_field_fiber U a).image _

@[expose] def liftObjectClass (W : GradedObject M S) : VFSemiring M S :=
  fieldClass M S ⟨W.1,liftFieldObject W.2⟩

omit [TopologicalSpace (X .vf)] in
theorem lift_cartesianProduct_iso :
    MixedDefinablyEquivalent M S (mixedProduct (ObjectLift.carrier U) (ObjectLift.carrier V))
      (ObjectLift.carrier (RVObject.cartesianProduct U V)) := by
  let P := RVObject.cartesianProduct U V
  let map : ∀ s, ObjectLift.Vars P s ≃ SumVariables (ObjectLift.Vars U) (ObjectLift.Vars V) s
    | .vf => finSumFinEquiv.symm
    | .rv => finSumFinEquiv.symm
  have hD : SortedDefinableOver M S.carrier (mixedProduct (ObjectLift.carrier U) (ObjectLift.carrier V)) :=
    ((ObjectLift.definable U).pullback_relabel (fun _ => Sum.inl)).inter
      ((ObjectLift.definable V).pullback_relabel (fun _ => Sum.inr))
  have eq : ObjectLift.carrier P = {w | (fun s => w s ∘ (map s).symm) ∈
      mixedProduct (ObjectLift.carrier U) (ObjectLift.carrier V)} := by
    ext w
    let r := w .rv
    let f := w .vf
    change (∃ a : P.carrier, a.val = r ∧ P.label a = M.rvMap ∘ f) ↔
      (∃ a : U.carrier, a.val = r ∘ finSumFinEquiv ∘ Sum.inl ∧
        U.label a = M.rvMap ∘ f ∘ finSumFinEquiv ∘ Sum.inl) ∧
      (∃ b : V.carrier, b.val = r ∘ finSumFinEquiv ∘ Sum.inr ∧
        V.label b = M.rvMap ∘ f ∘ finSumFinEquiv ∘ Sum.inr)
    constructor
    · rintro ⟨p,hp,hf⟩
      refine ⟨⟨RVObject.productLeft U V p,congrArg (· ∘ finSumFinEquiv ∘ Sum.inl) hp,?_⟩,
        ⟨RVObject.productRight U V p,congrArg (· ∘ finSumFinEquiv ∘ Sum.inr) hp,?_⟩⟩
      · funext i
        change U.label (RVObject.productLeft U V p) i = M.rvMap (f (finSumFinEquiv (.inl i)))
        simpa only [P,RVObject.cartesianProduct,RVObject.productLabel,Function.comp_apply,
          Equiv.symm_apply_apply,Sum.elim_inl] using congrFun hf (finSumFinEquiv (.inl i))
      · funext i
        change V.label (RVObject.productRight U V p) i = M.rvMap (f (finSumFinEquiv (.inr i)))
        simpa only [P,RVObject.cartesianProduct,RVObject.productLabel,Function.comp_apply,
          Equiv.symm_apply_apply,Sum.elim_inr] using congrFun hf (finSumFinEquiv (.inr i))
    · rintro ⟨⟨a,ha,hf⟩,b,hb,hg⟩
      let p : P.carrier := ⟨r,ha ▸ a.property,hb ▸ b.property⟩
      have eqA : RVObject.productLeft U V p = a := Subtype.ext ha.symm
      have eqB : RVObject.productRight U V p = b := Subtype.ext hb.symm
      refine ⟨p,rfl,?_⟩
      funext i
      obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
      change Sum.elim (U.label (RVObject.productLeft U V p)) (V.label (RVObject.productRight U V p))
        (finSumFinEquiv.symm (finSumFinEquiv i)) = M.rvMap (f (finSumFinEquiv i))
      rw [Equiv.symm_apply_apply,eqA,eqB]
      cases i with
      | inl i => exact congrFun hf i
      | inr i => exact congrFun hg i
  rw [eq]
  exact mixed_reindex_equivalent map _ hD

theorem lift_cartesianProduct_class :
    liftObjectClass ⟨k+l,RVObject.cartesianProduct U V⟩ =
      liftObjectClass ⟨k,U⟩ * liftObjectClass ⟨l,V⟩ := by
  unfold liftObjectClass fieldClass
  rw [← map_mul]
  apply field_scissors_sound M S
  exact VFRelation.product _ _ _ (lift_cartesianProduct_iso U V)

end GeneralizedEuler.Section5
