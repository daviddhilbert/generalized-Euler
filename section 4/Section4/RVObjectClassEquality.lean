module

public import Section4.RVScissorRealization
import all Section4.RVTaggedEquivalence
import all Section4.RVFamilyOperations
import all Section4.Factors
import all Section4.Objects
import all Section2.RVDefinableEquivalence

/-! In each fixed RV degree, an equality of object classes is realized
by a definable bijection of the original (untagged) objects. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}

theorem objectClass_eq_iff_definably_equivalent {k} (U W : RVObject M S k) :
    objectClass M S ⟨k,U⟩ = objectClass M S ⟨k,W⟩ ↔ RVDefinablyEquivalent M S.carrier U.carrier W.carrier := by
  constructor
  · intro eq
    have h := congrArg (RVFamily.realizeScissors M S) eq
    rw [RVFamily.realizeScissors_class,RVFamily.realizeScissors_class,RVFamily.cls_eq_iff] at h
    obtain ⟨f,hf⟩ := h
    let pack (D : RVObject M S k) : D.carrier ≃ (RVFamily.single D.carrier D.definable).Points :=
      { toFun := fun x => ⟨(),x⟩, invFun := fun x => x.2, left_inv := fun _ => rfl,
        right_inv := fun ⟨(),_⟩ => rfl }
    let e := (pack U).trans (f.trans (pack W).symm)
    refine ⟨e,?_⟩
    change isRVSet M S {w | ∃ x : U.carrier, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr}
    apply (congrArg (isRVSet M S (I := Fin U.arity ⊕ Fin W.arity)) _).mpr (hf () ())
    apply Set.ext
    intro w
    change (∃ x : U.carrier, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr) ↔
      ∃ (x : U.carrier) (y : W.carrier), x.val = w ∘ Sum.inl ∧ y.val = w ∘ Sum.inr ∧
        f (pack U x) = pack W y
    exact ⟨fun ⟨x,hx,hy⟩ => ⟨x,e x,hx,hy,((pack W).apply_symm_apply _).symm⟩,
      fun ⟨x,y,hx,hy,eq⟩ => ⟨x,hx,(congrArg (fun z => ((pack W).symm z).val) eq).trans hy⟩⟩
  · intro iso
    exact scissors_sound M S (RVRelation.iso U W iso)

end GeneralizedEuler.Section4
