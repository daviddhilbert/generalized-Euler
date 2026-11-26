module

public import Section4.ProductAssignment
import all Section4.AssignedScissors
import all Section4.LocalRVMeasure
import all Section4.Objects
import all Section4.Scissors

/-! Descend the assigned weights through the five relations defining the
concrete graded RV semiring. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z}
  {S : SortedSubstructure M} {P : Z .rv → Prop} {T : Type*} [CommSemiring T]

theorem singleton_equivalent {I H : Type} {D : Set (I → Z .rv)} {E : Set (H → Z .rv)}
    (hd : isRVSet M S D) (he : isRVSet M S E) (x : D) (y : E)
    (xd : ∀ a : D, a = x) (ye : ∀ b : E, b = y) : RVDefinablyEquivalent M S.carrier D E := by
  let f : D ≃ E := ⟨fun _ => y,fun _ => x,fun a => (xd a).symm,fun b => (ye b).symm⟩
  refine ⟨f,?_⟩
  have hg := rv_product_definable hd he
  unfold isRVSet at hg
  convert hg using 1
  ext w
  change (∃ a : D, a.val = w .rv ∘ Sum.inl ∧ y.val = w .rv ∘ Sum.inr) ↔
    w .rv ∘ Sum.inl ∈ D ∧ w .rv ∘ Sum.inr ∈ E
  exact ⟨fun ⟨a,eq,eq'⟩ => ⟨eq ▸ a.property,eq' ▸ y.property⟩,
    fun h => ⟨⟨_,h.1⟩,rfl,congrArg Subtype.val (ye ⟨_,h.2⟩).symm⟩⟩

namespace LocalRVMeasure
variable (μ : ∀ k, LocalRVMeasure M S P k T)
  (existsWeight : ∀ {k} (U : RVObject M S k), ∃ t, (μ k).assigned U.carrier t)
  (one : ∀ U : RVObject M S 0, (∃ x, U.carrier = {x}) → (μ 0).assigned U.carrier 1)
  (mul : ∀ {k l} (U : RVObject M S k) (V : RVObject M S l) {x y},
    (μ k).assigned U.carrier x → (μ l).assigned V.carrier y →
    (μ (k+l)).assigned (productSet U.carrier V.carrier) (x*y))

def descend : RVSemiring M S →+* T := by
  let w (U : GradedObject M S) := (μ U.1).objectWeight existsWeight U.2
  apply descendWeights M S w
  intro a b rel
  cases rel with
  | iso U V e => simpa [w] using (μ _).objectWeight_iso existsWeight U V e
  | zero U h => simpa [w] using (μ _).objectWeight_empty existsWeight U h
  | one U h => simpa [w,objectWeight] using (μ _).unique (existsWeight U).choose_spec (one U h)
  | cut U V W A B _ _ dj cov l r => simpa [w] using (μ _).objectWeight_cut existsWeight U V W A B dj cov l r
  | prod U V W equiv =>
    have h := (μ _).transfer equiv.symm (mul U V (existsWeight U).choose_spec (existsWeight V).choose_spec)
    simpa [w,objectWeight] using (μ _).unique (existsWeight W).choose_spec h

theorem descend_assigned {k} (U : RVObject M S k) {x} (hx : (μ k).assigned U.carrier x) :
    descend μ @existsWeight one @mul (objectClass M S ⟨k,U⟩) = x := by
  unfold descend
  rw [descendWeights_class]
  exact (μ k).unique (existsWeight U).choose_spec hx

end LocalRVMeasure
end GeneralizedEuler.Section4
