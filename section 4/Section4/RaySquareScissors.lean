module

public import Section4.BoundedIntervalScissors
public import Section4.GradedValues
import all Section4.ValueScissors
import all Section4.BoundedIntervalScissors

/-! The diagonal and the two open sectors give a positive scissor relation
for the square of the open ray, preserving its ambient degree two. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject
variable {F V : Type*} [Field F] [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V]
  {J : Language} [J.Structure V] (G : Submodule F V) (lang : ValueLanguage (J := J) G)

omit [LinearOrder V] [IsOrderedAddMonoid V] in
private theorem piece_image {k : ℕ} (f : (Fin k → V) → Fin k → V) (hf : (G : Set V).DefinableMap J f)
    (D : Set (Fin k → V)) (hd : (G : Set V).Definable J D) (inj : InjOn f D) :
    pieceClass (f '' D) (image_of_map f hf D hd) = pieceClass D hd := by
  simpa only [Set.image_id] using pieceClass_images f id hf (fun _ => Set.DefinableFun.proj J) D hd inj Function.injective_id.injOn

include lang in
theorem ray_square_scissors (dr : (G : Set V).Definable J (upperRay 0))
    (dp : (G : Set V).Definable J ({0} : Set (Fin 1 → V))) :
    (pieceClass _ dr)^2 = (pieceClass _ dr)^2 + ((pieceClass _ dr)^2 + pieceClass _ dp * pieceClass _ dr) := by
  let R := cartesian (upperRay (0 : V)) (upperRay 0)
  let D := cartesian ({0} : Set (Fin 1 → V)) (upperRay 0)
  have rdef := cartesian_definable dr dr
  have ddef := cartesian_definable dp dr
  have rm (x : Fin 2 → V) : x ∈ R ↔ 0 < x 0 ∧ 0 < x 1 := Iff.rfl
  have dm (x : Fin 2 → V) : x ∈ D ↔ x 0 = 0 ∧ 0 < x 1 := by
    change (x ∘ (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) ∘ Sum.inl ∈ ({0} : Set (Fin 1 → V)) ∧ 0 < x 1) ↔ _
    refine and_congr_left fun _ => ⟨fun e => congrFun e 0,fun h => ?_⟩
    apply funext; intro i; fin_cases i; exact h
  let f (x : Fin 2 → V) := ![x 0,x 0+x 1]
  let g (x : Fin 2 → V) := ![x 0+x 1,x 0]
  let h (x : Fin 2 → V) := ![x 1,x 1]
  have ff : (G : Set V).DefinableMap J f := by
    intro i; fin_cases i; exact Set.DefinableFun.proj J; exact lang.addFun (Set.DefinableFun.proj J) (Set.DefinableFun.proj J)
  have gg : (G : Set V).DefinableMap J g := by
    intro i; fin_cases i; exact lang.addFun (Set.DefinableFun.proj J) (Set.DefinableFun.proj J); exact Set.DefinableFun.proj J
  have hh : (G : Set V).DefinableMap J h := by intro i; fin_cases i <;> exact Set.DefinableFun.proj J
  have same {x y : Fin 2 → V} (e : x 0 = y 0) (d : x 1 = y 1) : x = y := by
    funext i; fin_cases i; exact e; exact d
  have fu : InjOn f R := by
    intro x _ y _ e
    have a : x 0 = y 0 := congrFun e 0
    have b : x 0 + x 1 = y 0 + y 1 := congrFun e 1
    exact same a (add_left_cancel (a ▸ b))
  have gu : InjOn g R := by
    intro x _ y _ e
    have a : x 0 = y 0 := congrFun e 1
    have b : x 0 + x 1 = y 0 + y 1 := congrFun e 0
    exact same a (add_left_cancel (a ▸ b))
  have hu : InjOn h D := fun x hx y hy e =>
    same (((dm x).mp hx).1.trans ((dm y).mp hy).1.symm) (congrFun e 0)
  have fm (x : Fin 2 → V) : x ∈ f '' R ↔ 0 < x 0 ∧ x 0 < x 1 := by
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨((rm y).mp hy).1,lt_add_of_pos_right _ ((rm y).mp hy).2⟩
    · rintro ⟨pos,lt⟩; exact ⟨![x 0,x 1-x 0],(rm _).mpr ⟨pos,sub_pos.mpr lt⟩,same rfl (add_sub_cancel _ _)⟩
  have gm (x : Fin 2 → V) : x ∈ g '' R ↔ 0 < x 1 ∧ x 1 < x 0 := by
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨((rm y).mp hy).1,lt_add_of_pos_right _ ((rm y).mp hy).2⟩
    · rintro ⟨pos,lt⟩; exact ⟨![x 1,x 0-x 1],(rm _).mpr ⟨pos,sub_pos.mpr lt⟩,same (add_sub_cancel _ _) rfl⟩
  have hm (x : Fin 2 → V) : x ∈ h '' D ↔ 0 < x 1 ∧ x 0 = x 1 := by
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨((dm y).mp hy).2,rfl⟩
    · rintro ⟨pos,eq⟩; exact ⟨![0,x 1],(dm _).mpr ⟨rfl,pos⟩,same eq.symm rfl⟩
  have partition : R = f '' R ∪ (g '' R ∪ h '' D) := by
    ext x; simp only [Set.mem_union,rm,fm,gm,hm]; grind
  have d₁ : Disjoint (g '' R) (h '' D) := Set.disjoint_left.mpr fun x hx hy =>
    ((gm x).mp hx).2.ne' ((hm x).mp hy).2
  have d₂ : Disjoint (f '' R) (g '' R ∪ h '' D) := by
    apply Set.disjoint_left.mpr; rintro x hx (hy|hy)
    · exact ((fm x).mp hx).2.not_gt ((gm x).mp hy).2
    · exact ((fm x).mp hx).2.ne ((hm x).mp hy).2
  have fr := image_of_map f ff R rdef
  have gr := image_of_map g gg R rdef
  have hd := image_of_map h hh D ddef
  rw [pow_two,← pieceClass_product dr dr,← pieceClass_product dp dr]
  calc pieceClass R rdef = pieceClass _ (fr.union (gr.union hd)) := by congr 1
       _ = _ := by rw [pieceClass_cut fr (gr.union hd) d₂,pieceClass_cut gr hd d₁,
                         piece_image G f ff R rdef fu,piece_image G g gg R rdef gu,piece_image G h hh D ddef hu]

end GeneralizedEuler.Section4
