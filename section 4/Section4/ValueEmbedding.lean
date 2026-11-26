module

public import Section4.ValueDescent
import all Section4.ValueScissors

/-! The positive value factor embeds into signed values coordinatewise. Finite
tags and every scissor relation are respected by the induced class map. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} {J H : Language} [J.Structure V] [H.Structure W] (G : Set V) (A : Set W)
  (ι : V ↪ W)
def mapTuples {I : Type*} (x : I → V) : I → W := ι ∘ x

theorem mapTuples_injective {I : Type*} : Function.Injective (mapTuples ι (I := I)) :=
  fun _ _ h => funext fun i => ι.injective (congrFun h i)

variable (defMap : ∀ {k} {D : Set (Fin k → V)}, G.Definable J D → A.Definable H (mapTuples ι '' D))

include defMap in
theorem definable_embedded_set {I : Type} [Fintype I] (D : Set (I → V)) (hd : G.Definable J D) :
    A.Definable H (mapTuples ι '' D) := by
  let e := Fintype.equivFin I
  have h := (defMap (hd.preimage_comp e)).preimage_comp e.symm
  convert h using 1
  ext w; constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x ∘ e.symm,by simpa [Function.comp_def] using hx,rfl⟩
  · rintro ⟨x,hx,eq⟩
    exact ⟨x ∘ e,hx,funext fun i => by simpa [mapTuples] using congrFun eq (e i)⟩

private theorem piece_eq {k} {D B : Set (Fin k → W)} (eq : D = B) (hd : A.Definable H D) (hb : A.Definable H B) :
    pieceClass D hd = pieceClass B hb := by subst B; rfl

def embeddingMeasure : PieceMeasure J G (SemiringOfSets (J := H) A) where
  weight D hd := pieceClass _ (defMap hd)
  empty _ := by convert pieceClass_empty (J := H) (A := A) using 2; simp
  one := by
    let y : Fin 0 → W := fun i => i.elim0
    have eq : mapTuples ι '' (Set.univ : Set (Fin 0 → V)) = {y} := by
      ext z
      exact ⟨fun _ => Subsingleton.elim _ _,fun _ => ⟨fun i => i.elim0,Set.mem_univ _,Subsingleton.elim _ _⟩⟩
    have hy : A.Definable H {y} := eq ▸ defMap (Set.definable_univ (A := G) (L := J))
    exact (piece_eq A eq _ hy).trans (pieceClass_degree_zero y hy)
  cut D B hd hb disj := by
    have h := pieceClass_cut (defMap hd) (defMap hb) (Set.disjoint_image_of_injective (mapTuples_injective ι) disj)
    exact (piece_eq A (Set.image_union ..) _ _).trans h
  iso D B hd hb e graph := by
    let d := Equiv.Set.imageOfInjOn _ D (mapTuples_injective ι).injOn
    let b := Equiv.Set.imageOfInjOn _ B (mapTuples_injective ι).injOn
    let f := d.symm.trans (e.trans b)
    apply pieceClass_iso _ _ f
    convert definable_embedded_set G A ι defMap _ graph using 1
    ext w; constructor
    · rintro ⟨x,hx,hy⟩
      obtain ⟨z,rfl⟩ := d.surjective x
      refine ⟨Sum.elim z.val (e z).val,⟨z,rfl,rfl⟩,funext fun i => ?_⟩
      cases i with
      | inl i => exact congrFun hx i
      | inr j =>
        change (b (e (d.symm (d z)))).val = _ at hy
        rw [d.symm_apply_apply] at hy; exact congrFun hy j
    · rintro ⟨x,⟨z,hz,he⟩,rfl⟩
      refine ⟨d z,congrArg (mapTuples ι) hz,?_⟩
      change (b (e (d.symm (d z)))).val = _
      rw [d.symm_apply_apply]; exact congrArg (mapTuples ι) he
  prod D B hd hb := by
    have eq : mapTuples ι '' cartesian D B = cartesian (mapTuples ι '' D) (mapTuples ι '' B) := by
      ext w; constructor
      · rintro ⟨z,⟨hx,hy⟩,rfl⟩; exact ⟨⟨_,hx,rfl⟩,_,hy,rfl⟩
      · rintro ⟨⟨x,hx,ex⟩,⟨y,hy,ey⟩⟩
        let z := cartesianEquiv D B (⟨x,hx⟩,⟨y,hy⟩)
        refine ⟨z.val,z.property,funext fun i => ?_⟩
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
        cases j with
        | inl i => simpa [z,mapTuples,cartesianEquiv] using congrFun ex i
        | inr j => simpa [z,mapTuples,cartesianEquiv] using congrFun ey j
    exact (piece_eq A eq _ _).trans (pieceClass_product (defMap hd) (defMap hb))

end GeneralizedEuler.Section4.ValueObject
