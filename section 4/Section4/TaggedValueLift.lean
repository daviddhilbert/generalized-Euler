module

public import Section4.ValueTagComparison
public import Section4.ValuePullback
public import Section4.MatchingRectangles
import all Section4.ValueTagComparison
import all Section4.ValuePullback
import all Section4.Factors
import all Section4.Objects

/-! Lemma 4.12 for finite tagged unions. Each tag-pair graph provides a
single value morphism. Gluing its lift preserves the original tag and
value action. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {J H : Language} {F Γ : Type*} [H.Structure Γ] {Z : TCsort → Type*}
  (M : SortedStructure J F Z) (S : SortedSubstructure M) (v : Z .rv → Γ) (A : Set Γ)
local notation "sh" => sharp M v

theorem tagged_value_morphism_lift
    (lift : ∀ {k} (D C : Set (Fin k → Γ)), A.Definable H D → A.Definable H C →
      ∀ e : D ≃ C, A.Definable H {w : Fin k ⊕ Fin k → Γ | ∃ a : D, a.val = w ∘ Sum.inl ∧ (e a).val = w ∘ Sum.inr} →
        ∃ f : sh D ≃ sh C, SortedDefinableOver M S.carrier (rvGraph fun x => (f x).val) ∧
          ∀ x : sh D, v ∘ (f x).val = (e ⟨v ∘ x.val,by exact x.property.2⟩).val)
    {k} (U W : Over (J := H) A k) (e : (Σ i, U.piece i) ≃ (Σ j, W.piece j))
    (he : ∀ i j, A.Definable H (sliceGraph U.piece W.piece e i j)) :
    ∃ f : (Σ i, sh (U.piece i)) ≃ (Σ j, sh (W.piece j)),
      (∀ i j, isRVSet M S (sliceGraph (fun i => sh (U.piece i)) (fun j => sh (W.piece j)) f i j)) ∧
      ∀ x, e ⟨x.1,v ∘ x.2.val,by exact x.2.property.2⟩ =
        ⟨(f x).1,v ∘ (f x).2.val,by exact (f x).2.property.2⟩ := by
  let R i j (a b : Fin k → Γ) : Prop := ∃ (ha : a ∈ U.piece i) (hb : b ∈ W.piece j),
    e ⟨i,a,ha⟩ = ⟨j,b,hb⟩
  have graph i j (w : Fin k ⊕ Fin k → Γ) : w ∈ sliceGraph U.piece W.piece e i j ↔ R i j (w ∘ Sum.inl) (w ∘ Sum.inr) := by
    constructor
    · rintro ⟨⟨a,ha⟩,rfl,⟨b,hb⟩,rfl,h⟩
      exact ⟨ha,hb,h⟩
    · rintro ⟨ha,hb,h⟩
      exact ⟨⟨_,ha⟩,rfl,⟨_,hb⟩,rfl,h⟩
  have single i j {a b c} (h : R i j a b) (h' : R i j a c) : b=c := by
    obtain ⟨_,_,l⟩ := h; obtain ⟨_,_,r⟩ := h'
    exact congrArg Subtype.val (Sigma.mk.inj_iff.mp (l.symm.trans r)).2.eq
  have inj i j {a b c} (h : R i j a c) (h' : R i j b c) : a=b := by
    obtain ⟨_,_,l⟩ := h; obtain ⟨_,_,r⟩ := h'
    exact congrArg Subtype.val (Sigma.mk.inj_iff.mp (e.injective (l.trans r.symm))).2.eq
  let D i j := {a | ∃ b, R i j a b}
  let C i j := {b | ∃ a, R i j a b}
  let p i j : D i j ≃ C i j := matchingGraphEquiv _ (fun h h' => single i j h h') (fun h h' => inj i j h h')
  have law i j (a : D i j) (b : Fin k → Γ) : (p i j a).val = b ↔ R i j a.val b :=
    matchingGraphEquiv_iff _ _ _ _ _
  have localLift i j : ∃ f : sh (D i j) ≃ sh (C i j),
      SortedDefinableOver M S.carrier (rvGraph fun x => (f x).val) ∧
      ∀ x, R i j (v ∘ x.val) (v ∘ (f x).val) := by
    have hd : A.Definable H (D i j) := by
      convert (he i j).image_comp Sum.inl using 1
      ext a
      exact ⟨fun ⟨b,h⟩ => ⟨Sum.elim a b,(graph i j (Sum.elim a b)).mpr h,rfl⟩,
        fun ⟨w,h,eq⟩ => eq ▸ ⟨_,(graph i j w).mp h⟩⟩
    have hc : A.Definable H (C i j) := by
      convert (he i j).image_comp Sum.inr using 1
      ext b
      exact ⟨fun ⟨a,h⟩ => ⟨Sum.elim a b,(graph i j (Sum.elim a b)).mpr h,rfl⟩,
        fun ⟨w,h,eq⟩ => eq ▸ ⟨_,(graph i j w).mp h⟩⟩
    have hp : A.Definable H {w : Fin k ⊕ Fin k → Γ | ∃ a : D i j,
        a.val = w ∘ Sum.inl ∧ (p i j a).val = w ∘ Sum.inr} := by
      convert he i j using 1
      ext w; rw [graph]
      exact ⟨fun ⟨a,h,r⟩ => h ▸ (law i j a _).mp r,fun h => ⟨⟨_,_,h⟩,rfl,(law i j _ _).mpr h⟩⟩
    obtain ⟨f,hf,lf⟩ := lift _ _ hd hc (p i j) hp
    exact ⟨f,hf,fun x => (law i j ⟨_,x.property.2⟩ _).mp (lf x).symm⟩
  choose f hf lf using localLift
  let X := Σ i, sh (U.piece i)
  let Y := Σ j, sh (W.piece j)
  let src (x : X) : (Σ i, U.piece i) := ⟨x.1,v ∘ x.2.val,x.2.property.2⟩
  let dst (y : Y) : (Σ j, W.piece j) := ⟨y.1,v ∘ y.2.val,y.2.property.2⟩
  let T (x : X) (y : Y) : Prop := ∃ z : sh (D x.1 y.1), z.val=x.2.val ∧ (f x.1 y.1 z).val=y.2.val
  have comm {x : X} {y : Y} (h : T x y) : e (src x) = dst y := by
    obtain ⟨z,hz,eq⟩ := h
    have l := lf x.1 y.1 z
    rw [hz,eq] at l
    exact l.choose_spec.choose_spec
  have forward (x : X) : ∃ y, T x y := by
    let j := (e (src x)).1
    let a := (e (src x)).2
    have h : e (src x) = ⟨j,a⟩ := rfl
    have r : R x.1 j (v ∘ x.2.val) a.val := ⟨_,a.property,h⟩
    let z : sh (D x.1 j) := ⟨x.2.val,x.2.property.1,_,r⟩
    let t := f x.1 j z
    obtain ⟨_,ht,_⟩ := lf x.1 j z
    exact ⟨⟨j,t.val,t.property.1,ht⟩,z,rfl,rfl⟩
  have backward (y : Y) : ∃ x, T x y := by
    let i := (e.symm (dst y)).1
    let a := (e.symm (dst y)).2
    have h : e.symm (dst y) = ⟨i,a⟩ := rfl
    have r : R i y.1 a.val (v ∘ y.2.val) := ⟨a.property,_,(e.symm_apply_eq.mp h).symm⟩
    let t : sh (C i y.1) := ⟨y.2.val,y.2.property.1,_,r⟩
    let z := (f i y.1).symm t
    have ft : f i y.1 z = t := Equiv.apply_symm_apply _ _
    obtain ⟨hz,_,_⟩ := lf i y.1 z
    exact ⟨⟨i,z.val,z.property.1,hz⟩,z,rfl,congrArg Subtype.val ft⟩
  have uniq {x : X} {y z : Y} (h : T x y) (h' : T x z) : y=z := by
    obtain ⟨i,y⟩ := y; obtain ⟨j,z⟩ := z
    obtain rfl : i=j := congrArg Sigma.fst ((comm h).symm.trans (comm h'))
    obtain ⟨a,ha,ea⟩ := h; obtain ⟨b,hb,eb⟩ := h'
    have eq : a=b := Subtype.ext (ha.trans hb.symm)
    exact congrArg (Sigma.mk i) (Subtype.ext (ea.symm.trans (eq ▸ eb)))
  have uniqueSrc {x z : X} {y : Y} (h : T x y) (h' : T z y) : x=z := by
    obtain ⟨i,x⟩ := x; obtain ⟨j,z⟩ := z
    obtain rfl : i=j := congrArg Sigma.fst (e.injective ((comm h).trans (comm h').symm))
    obtain ⟨a,ha,ea⟩ := h; obtain ⟨b,hb,eb⟩ := h'
    have eq : a=b := (f i y.1).injective (Subtype.ext (ea.trans eb.symm))
    exact congrArg (Sigma.mk i) (Subtype.ext (ha.symm.trans (eq ▸ hb)))
  let g : X ≃ Y :=
    { toFun := fun x => (forward x).choose
      invFun := fun y => (backward y).choose
      left_inv := fun x => uniqueSrc (backward _).choose_spec (forward x).choose_spec
      right_inv := fun y => uniq (forward _).choose_spec (backward y).choose_spec }
  have spec (x : X) : T x (g x) := (forward x).choose_spec
  refine ⟨g,?_,fun x => comm (spec x)⟩
  intro i j
  unfold isRVSet
  convert hf i j using 1
  ext w
  change (∃ x : sh (U.piece i), x.val=w .rv ∘ Sum.inl ∧ ∃ y : sh (W.piece j),
    y.val=w .rv ∘ Sum.inr ∧ g ⟨i,x⟩=⟨j,y⟩) ↔
    ∃ z : sh (D i j), z.val=w .rv ∘ Sum.inl ∧ (f i j z).val=w .rv ∘ Sum.inr
  constructor
  · rintro ⟨x,hx,y,hy,eq⟩
    obtain ⟨z,hz,ez⟩ := eq ▸ spec ⟨i,x⟩
    exact ⟨z,hz.trans hx,ez.trans hy⟩
  · rintro ⟨z,hz,eq⟩
    obtain ⟨hs,ht,_⟩ := lf i j z
    let x : sh (U.piece i) := ⟨z.val,z.property.1,hs⟩
    let y : sh (W.piece j) := ⟨(f i j z).val,(f i j z).property.1,ht⟩
    exact ⟨x,hz,y,eq,uniq (spec ⟨i,x⟩) (show T ⟨i,x⟩ ⟨j,y⟩ from ⟨z,rfl,rfl⟩)⟩

end GeneralizedEuler.Section4
