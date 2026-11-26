module

public import Section4.ProjectedFrame
public import Section4.ValueScissors
public import Section4.CommonValueRefinement
import all Section4.ProjectedFrame
import all Section4.DefinableValueFrames
import all Section4.ValueStratification

/-! An injective graph projection preserves the value class of its affine piece. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {G : Submodule F V}
  {J : Language} [J.Structure V] {r k n : ℕ} {A : ValueFrame G r n} {p : Fin k → Fin n}

theorem span_directions_le {I H : Type*} [Fintype I] (a : Matrix H I F) (z : I → V) :
    Submodule.span F (Set.range (actRows a z)) ≤ Submodule.span F (Set.range z) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem independent_after_matrix (U : (Matrix (Fin r) (Fin r) F)ˣ) (z : Fin r → V)
    (h : LinearIndependent F z) : LinearIndependent F (actRows U.val z) := by
  have eq : Submodule.span F (Set.range (actRows U.val z)) = Submodule.span F (Set.range z) := by
    apply le_antisymm (span_directions_le _ _)
    have back := span_directions_le U.inv (actRows U.val z)
    rwa [← actRows_mul,U.inv_val,actRows_one] at back
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin r) = Module.finrank F (Submodule.span F (Set.range (actRows U.val z)))
  rw [eq]
  exact linearIndependent_iff_card_eq_finrank_span.mp h

namespace ProjectionBasis
variable (q : ProjectionBasis A p)

theorem forward_independent (z : Fin r → V) (h : LinearIndependent F (G.mkQ ∘ z)) :
    LinearIndependent F (G.mkQ ∘ q.forward z) := by
  have eq : G.mkQ ∘ q.forward z = actRows q.minor.val (G.mkQ ∘ z) := by
    funext i
    change G.mkQ (actRows q.minor.val z i + (q.offset i).val) = _
    rw [map_add,show G.mkQ (q.offset i).val = 0 from (Submodule.Quotient.mk_eq_zero G).mpr (q.offset i).property,add_zero]
    exact congrFun (actRows_map G.mkQ q.minor.val z) i
  rw [eq]; exact independent_after_matrix q.minor _ h

theorem forward_definable (lang : ValueLanguage (J := J) G) : (G : Set V).DefinableMap J q.forward := by
  intro i
  have eq : (fun z => q.forward z i) = fun z => A.eval z (p (q.free i)) := funext fun z => congrFun (q.forward_eq z) i
  rw [eq]; exact lang.frame A _

def projectedPiece (lang : ValueLanguage (J := J) G) (D : Set (Fin r → V))
    (hd : (G : Set V).Definable J D) (ind : ∃ α ∈ D, LinearIndependent F (G.mkQ ∘ α)) : DefinablePiece J G k where
  rank := r
  frame := q.frame
  domain := q.forward '' D
  definable := image_of_map _ (q.forward_definable lang) _ hd
  independent := by
    obtain ⟨α,hα,hi⟩ := ind
    exact ⟨_,⟨_,hα,rfl⟩,q.forward_independent α hi⟩

theorem forward_class (lang : ValueLanguage (J := J) G) (D : Set (Fin r → V)) (hd : (G : Set V).Definable J D) :
    pieceClass (q.forward '' D) (image_of_map _ (q.forward_definable lang) D hd) = pieceClass D hd := by
  have hid : (G : Set V).DefinableMap J (id : (Fin r → V) → _) := fun _ => Set.DefinableFun.proj J
  have eq := pieceClass_images q.forward id (q.forward_definable lang) hid D hd q.forward_bijective.1.injOn Function.injective_id.injOn
  simpa using eq

end ProjectionBasis
end GeneralizedEuler.Section4
