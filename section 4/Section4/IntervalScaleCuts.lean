module

public import Section4.IntervalCutScissors
import all Section4.BoundedIntervalScissors
import all Section4.ValueScissors

/-! Positive cut identities on interval classes, using the scales of
the given widths. All intermediate endpoints lie in the fixed base. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {J : Language} [J.Structure V] (G : Submodule F V) (lang : ValueLanguage (J := J) G)
  (leDef : ∀ t ∈ G, (G : Set V).Definable J {x : Unit → V | x () ≤ t})
  (dom : ∀ t ∈ G, (G : Set V).Definable J (intervalPiece t))
  (dp : (G : Set V).Definable J ({0} : Set (Fin 1 → V)))

include lang leDef in
theorem interval_class_of_same_scale (a b : V) (oa : a ∈ G) (ob : b ∈ G) (ha : 0<a) (hb : 0<b)
    (ab : a ∈ scaleSpace F b) (ba : b ∈ scaleSpace F a) :
    pieceClass _ (dom a oa) = pieceClass _ (dom b ob) := by
  obtain ⟨q,image,maps⟩ := comparable_widths_definable G lang leDef oa ob ha hb ab ba
  let f (x : Fin 1 → V) (i : Fin 1) := q (x i)
  have hf : (G : Set V).DefinableMap J f := fun i =>
    maps.comp (g := fun x _ => x i) (fun _ => Set.DefinableFun.proj J)
  have surj : f '' intervalPiece a = intervalPiece b := by
    ext x; constructor
    · rintro ⟨y,hy,rfl⟩
      change q (y 0) ∈ Ioo 0 b
      rw [← image]; exact Set.mem_image_of_mem q hy
    · intro h
      obtain ⟨z,hz,ez⟩ : x 0 ∈ q '' Ioo 0 a := image.symm ▸ h
      exact ⟨fun _ => z,hz,funext fun i => by simpa [f,Subsingleton.elim i 0] using ez⟩
  have eq := pieceClass_images f id hf (fun _ => Set.DefinableFun.proj J) _ (dom a oa)
    (fun x _ y _ e => funext fun i => q.injective (congrFun e i)) Function.injective_id.injOn
  simpa only [surj,Set.image_id] using eq.symm

include lang leDef in
theorem interval_midpoint_scissors (a : V) (oa : a ∈ G) (ha : 0<a) :
    pieceClass _ (dom a oa) = pieceClass _ (dom a oa) + (pieceClass _ (dom a oa) + pieceClass _ dp) := by
  have oa' := G.add_mem oa oa
  have ha' := add_pos ha ha
  have large : a+a ∈ scaleSpace F a := (scaleSpace F a).add_mem (self_mem_scaleSpace F a) (self_mem_scaleSpace F a)
  have small : a ∈ scaleSpace F (a+a) := scaleSpace_interval F ha.le (le_add_of_nonneg_right ha.le)
  have same := interval_class_of_same_scale G lang leDef dom (a+a) a oa' oa ha' ha large small
  have eq := bounded_interval_scissors G lang a a oa ha ha (dom a oa) (dom a oa) (dom _ oa') dp
  rw [same] at eq
  simpa only [add_comm (pieceClass _ dp)] using eq

include lang leDef in
theorem smaller_interval_scissors (a b : V) (oa : a ∈ G) (ob : b ∈ G) (ha : 0<a) (hb : 0<b)
    (strict : b ∉ scaleSpace F a) :
    pieceClass _ (dom b ob) = pieceClass _ (dom b ob) + (pieceClass _ (dom a oa) + pieceClass _ dp) := by
  have big : a+a < b := lt_of_not_ge (fun h => strict
    (scaleSpace_mono F ((scaleSpace F a).add_mem (self_mem_scaleSpace F a) (self_mem_scaleSpace F a))
      (scaleSpace_interval F hb.le h)))
  have small : a < b-a := lt_sub_iff_add_lt.mpr big
  have pos := ha.trans small
  have old := G.sub_mem ob oa
  have ab : b-a ∈ scaleSpace F b := scaleSpace_interval F pos.le (sub_le_self _ ha.le)
  have ba : b ∈ scaleSpace F (b-a) := by
    have h := (scaleSpace F (b-a)).add_mem (scaleSpace_interval F ha.le small.le) (self_mem_scaleSpace F (b-a))
    simpa only [add_sub_cancel] using h
  have same := interval_class_of_same_scale G lang leDef dom (b-a) b old ob pos hb ab ba
  have eq := bounded_interval_scissors G lang a (b-a) oa ha pos (dom _ oa) (dom _ old)
    (dom _ (G.add_mem oa old)) dp
  rw [same] at eq
  simpa only [add_sub_cancel,add_assoc,add_comm,add_left_comm] using eq

end GeneralizedEuler.Section4
