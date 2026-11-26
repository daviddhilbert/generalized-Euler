module

public import Section4.ValueRefinement
public import Section4.ValueMembershipPartition
import all Section4.ValueScissors
import all Section4.ValueStratification
import all Section4.ValuePadding

/-! Summing the projected value classes over an arbitrary simultaneous subdivision. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {J : Language} [J.Structure V]
  {G : Submodule F V} {n l : ℕ}
  (lang : ValueLanguage (J := J) G) (a : DefinablePiece J G n)
  (c : Fin l → DefinablePiece J G n)

include lang in
theorem subdivided_value_class (active : Fin l → Bool)
    (unique : ∀ γ, ∃! t, γ ∈ (c t).support)
    (membership : ∀ t γ, γ ∈ (c t).support → (γ ∈ a.support ↔ active t = true)) :
    pieceClass a.domain a.definable =
      ∑ t : {t // active t = true}, pieceClass (c t.val).domain (c t.val).definable *
        eValue G ^ (a.rank - (c t.val).rank) := by
  classical
  let I := {t // active t = true}
  let f (t : I) (z : Fin (c t.val).rank → V) := (c t.val).frame.eval z ∘ a.frame.free
  let D (t : I) := f t '' (c t.val).domain
  have hd (t : I) : (G : Set V).Definable J (D t) :=
    image_of_map _ (projected_value_definable lang _ _) _ (c t.val).definable
  have parent (t : I) {γ} (h : γ ∈ (c t.val).support) : γ ∈ a.support :=
    (membership t.val γ h).mpr t.property
  have restore (t : I) (x : Fin (c t.val).rank → V) (hx : x ∈ (c t.val).domain) :
      a.frame.eval (f t x) = (c t.val).frame.eval x := by
    obtain ⟨y,_,hy⟩ := parent t (show (c t.val).frame.eval x ∈ (c t.val).support from ⟨x,hx,rfl⟩)
    change a.frame.eval ((c t.val).frame.eval x ∘ a.frame.free) = _
    rw [← hy,a.frame.project_eval]
  have cover : ⋃ t, D t = a.domain := by
    ext x; rw [Set.mem_iUnion]
    constructor
    · rintro ⟨t,z,hz,rfl⟩
      obtain ⟨y,hy,eq⟩ := parent t (show (c t.val).frame.eval z ∈ (c t.val).support from ⟨z,hz,rfl⟩)
      change (c t.val).frame.eval z ∘ a.frame.free ∈ a.domain
      rwa [← eq,a.frame.project_eval]
    · intro hx
      obtain ⟨t,ht,_⟩ := unique (a.frame.eval x)
      have on := (membership t _ ht).mp ⟨x,hx,rfl⟩
      obtain ⟨z,hz,eq⟩ := ht
      exact ⟨⟨t,on⟩,z,hz,(congrArg (· ∘ a.frame.free) eq).trans (a.frame.project_eval x)⟩
  have disj : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j neq
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ ⟨w,hw,eq⟩
    have same := (restore j w hw).symm.trans ((congrArg a.frame.eval eq).trans (restore i z hz))
    exact neq (Subtype.ext ((unique _).unique ⟨z,hz,rfl⟩ ⟨w,hw,same⟩))
  have sum := pieceClass_partition D hd disj
  refine ((class_congr G cover.symm _ _).trans sum).trans (Finset.sum_congr rfl fun t _ => ?_)
  obtain ⟨x,hx,hi⟩ := (c t.val).independent
  have hit := parent t (show (c t.val).frame.eval x ∈ (c t.val).support from ⟨x,hx,rfl⟩)
  exact projected_value_class lang _ _ x hi (Set.image_subset_range _ _ hit) _ _

end GeneralizedEuler.Section4.ValueObject
