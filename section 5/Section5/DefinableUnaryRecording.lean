module

public import Section5.UnaryChainRules
public import Section5.DefinableOutputCoordinate

/-! The first relatively unary factor retains the other field
coordinates and carries the output RV tuple. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ} {I J : Type} [Finite J]
  {A : MixedCarrier X n I} {B : MixedCarrier X n J} (f : MixedGraphIso M S A B)

theorem definable_record_output_coordinate (i j : Fin n)
    (determines : ∀ x y : A, (∀ k, k ≠ i → x.val .vf k = y.val .vf k) →
      (f.equiv x).val .vf j = (f.equiv y).val .vf j → (f.equiv x).val .vf = (f.equiv y).val .vf) :
    ∃ (C : MixedCarrier X n J) (g : MixedGraphIso M S A C), FixesOutside g {i} ∧
      (∀ x : A, (g.equiv x).val .vf i = (f.equiv x).val .vf j) := by
  let update (x : A) := recordOutputAssignment i j x.val (f.equiv x).val
  have injective : Function.Injective update := by
    intro x y e
    have ec := congrFun e .vf
    have head (k : Fin n) (hk : k ≠ i) : x.val .vf k = y.val .vf k := by
      simpa only [update,recordOutputAssignment,Function.update_of_ne hk] using congrFun ec k
    have lead : (f.equiv x).val .vf j = (f.equiv y).val .vf j := by
      simpa only [update,recordOutputAssignment,Function.update_self] using congrFun ec i
    have field := determines x y head lead
    apply f.equiv.injective
    apply Subtype.ext
    funext s k
    cases s
    · exact congrFun field k
    · exact congrFun (congrFun e .rv) k
  have gDef := recordOutputAssignment_graph i j _ f.definable
  have same : DefinableRelation M S.carrier (fun a b => ∃ h : a ∈ A, update ⟨a,h⟩ = b) := by
    apply gDef.congr
    intro a b
    constructor
    · rintro ⟨_,⟨h,rfl⟩,e⟩
      exact ⟨h,e⟩
    · rintro ⟨h,e⟩
      exact ⟨_,⟨h,rfl⟩,e⟩
  let g := MixedGraphIso.toRange update injective same
  refine ⟨Set.range update,g,?_,?_⟩
  · intro x k hk
    exact Function.update_of_ne (fun e => hk (Finset.mem_singleton.2 e)) _ _
  · intro x
    exact Function.update_self _ _ _

end GeneralizedEuler.Section5
