module

public import Section4.FiniteScissors
public import Section4.DefinableValueFrames
import all Section4.Factors

public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder
namespace ValueObject
variable {V : Type*} {J : Language} [J.Structure V] {A : Set V} {k : ℕ}

abbrev single (D : Set (Fin k → V)) (hd : A.Definable J D) : Over (J := J) A k :=
  ⟨1,fun _ => D,fun _ => hd⟩

def singlePoints {D : Set (Fin k → V)} (hd : A.Definable J D) : (single D hd).points A ≃ D where
  toFun x := x.2
  invFun x := ⟨0,x⟩
  left_inv x := by rcases x with ⟨i,x⟩; have e : i = 0 := Subsingleton.elim _ _; subst i; rfl
  right_inv _ := rfl

def pieceClass (D : Set (Fin k → V)) (hd : A.Definable J D) : SemiringOfSets (J := J) A :=
  (ringConGen (Relation (J := J) A)).mk' (MvPolynomial.X ⟨k,single D hd⟩)

theorem relation_sound {a b} (h : Relation (J := J) A a b) :
    (ringConGen (Relation (J := J) A)).mk' a = (ringConGen (Relation (J := J) A)).mk' b :=
  Quotient.sound (RingConGen.Rel.of _ _ h)

theorem pieceClass_iso {D E : Set (Fin k → V)} (hd : A.Definable J D) (he : A.Definable J E)
    (f : D ≃ E) (graph : A.Definable J {x : Fin k ⊕ Fin k → V |
      ∃ t : D, t.val = x ∘ Sum.inl ∧ (f t).val = x ∘ Sum.inr}) :
    pieceClass D hd = pieceClass E he := by
  apply relation_sound
  apply Relation.iso
  let e := (singlePoints hd).trans (f.trans (singlePoints he).symm)
  refine ⟨e,fun i j => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  convert graph using 1
  ext x
  constructor
  · rintro ⟨t,ht,b,hb,eq⟩
    exact ⟨t,ht,(congrArg (fun p => ((singlePoints he) p).val) eq).trans hb⟩
  · rintro ⟨t,ht,eq⟩
    exact ⟨t,ht,f t,eq,rfl⟩

theorem graph_of_map {I H : Type*} [Finite I] [Finite H] (f : (I → V) → (H → V))
    (hf : A.DefinableMap J f) (D : Set (I → V)) (hd : A.Definable J D) :
    A.Definable J {x : I ⊕ H → V | x ∘ Sum.inl ∈ D ∧ f (x ∘ Sum.inl) = x ∘ Sum.inr} := by
  have he := Set.definable_iInter_of_finite (fun j : H =>
    ((hf j).comp (g := fun x : I ⊕ H → V => x ∘ Sum.inl) (fun i => Set.DefinableFun.proj J)).ofPred_eq
      (Set.DefinableFun.proj J (i := Sum.inr j)))
  convert (hd.preimage_comp Sum.inl).inter he using 1
  ext x; simp [funext_iff]

theorem image_of_map {I H : Type*} [Finite I] [Finite H] (f : (I → V) → (H → V))
    (hf : A.DefinableMap J f) (D : Set (I → V)) (hd : A.Definable J D) : A.Definable J (f '' D) := by
  convert (graph_of_map f hf D hd).image_comp Sum.inr using 1
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨Sum.elim t (f t),⟨ht,rfl⟩,rfl⟩
  · rintro ⟨t,⟨ht,eq⟩,rfl⟩; exact ⟨_,ht,eq⟩

theorem pieceClass_images {m} (f g : (Fin m → V) → (Fin k → V))
    (hf : A.DefinableMap J f) (hg : A.DefinableMap J g)
    (D : Set (Fin m → V)) (hd : A.Definable J D) (injf : Set.InjOn f D) (injg : Set.InjOn g D) :
    pieceClass (f '' D) (image_of_map f hf D hd) = pieceClass (g '' D) (image_of_map g hg D hd) := by
  let ef := Equiv.Set.imageOfInjOn f D injf
  let eg := Equiv.Set.imageOfInjOn g D injg
  let e := ef.symm.trans eg
  let pair (x : Fin m → V) := Sum.elim (f x) (g x)
  have hp : A.DefinableMap J pair := by intro i; cases i with | inl i => exact hf i | inr j => exact hg j
  apply pieceClass_iso _ _ e
  convert image_of_map pair hp D hd using 1
  ext x
  constructor
  · rintro ⟨a,ha,hb⟩
    obtain ⟨t,rfl⟩ := ef.surjective a
    refine ⟨t.val,t.property,funext fun i => ?_⟩
    cases i with
    | inl i => exact congrFun ha i
    | inr i =>
      change (eg (ef.symm (ef t))).val = _ at hb
      rw [ef.symm_apply_apply] at hb
      exact congrFun hb i
  · rintro ⟨t,ht,rfl⟩
    let a : D := ⟨t,ht⟩
    exact ⟨ef a,rfl,congrArg (fun z : D => (eg z).val) (ef.symm_apply_apply a)⟩

def cartesian {l} (D : Set (Fin k → V)) (E : Set (Fin l → V)) :=
  {x : Fin (k+l) → V | x ∘ finSumFinEquiv ∘ Sum.inl ∈ D ∧ x ∘ finSumFinEquiv ∘ Sum.inr ∈ E}

theorem cartesian_definable {l} {D : Set (Fin k → V)} {E : Set (Fin l → V)}
    (hd : A.Definable J D) (he : A.Definable J E) : A.Definable J (cartesian D E) :=
  (hd.preimage_comp (finSumFinEquiv ∘ Sum.inl)).inter (he.preimage_comp (finSumFinEquiv ∘ Sum.inr))

def cartesianEquiv {l} (D : Set (Fin k → V)) (E : Set (Fin l → V)) : D × E ≃ cartesian D E where
  toFun x := ⟨Sum.elim x.1.val x.2.val ∘ finSumFinEquiv.symm,by
    simp [cartesian,Function.comp_def]⟩
  invFun x := (⟨_,x.property.1⟩,⟨_,x.property.2⟩)
  left_inv x := Prod.ext (Subtype.ext (by funext i; simp)) (Subtype.ext (by funext i; simp))
  right_inv x := by
    apply Subtype.ext; funext i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp

theorem pieceClass_product {l} {D : Set (Fin k → V)} {E : Set (Fin l → V)}
    (hd : A.Definable J D) (he : A.Definable J E) :
    pieceClass (cartesian D E) (cartesian_definable hd he) = pieceClass D hd * pieceClass E he := by
  let h := cartesian_definable hd he
  let e := ((Equiv.prodCongr (singlePoints hd) (singlePoints he)).trans
    (cartesianEquiv D E)).trans (singlePoints h).symm
  apply relation_sound
  apply Relation.prod
  refine ⟨e,fun i j t => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  have ht : t = 0 := Subsingleton.elim _ _
  subst i; subst j; subst t
  let D' := {x : Fin k ⊕ Fin l → V | x ∘ Sum.inl ∈ D ∧ x ∘ Sum.inr ∈ E}
  let f (x : Fin k ⊕ Fin l → V) := x ∘ finSumFinEquiv.symm
  have hf : A.DefinableMap J f := fun i => Set.DefinableFun.proj J
  have hg := graph_of_map f hf D' ((hd.preimage_comp Sum.inl).inter (he.preimage_comp Sum.inr))
  convert hg using 1
  ext w
  have eta : Sum.elim (w ∘ Sum.inl ∘ Sum.inl) (w ∘ Sum.inl ∘ Sum.inr) = w ∘ Sum.inl := by
    funext j; cases j <;> rfl
  constructor
  · rintro ⟨x,y,hx,hy,z,hz,eq⟩
    refine ⟨⟨hx ▸ x.property,hy ▸ y.property⟩,?_⟩
    have same := congrArg (fun p => ((singlePoints h) p).val) eq
    change Sum.elim x.val y.val ∘ finSumFinEquiv.symm = z.val at same
    rw [hx,hy,hz] at same
    rwa [eta] at same
  · rintro ⟨⟨hx,hy⟩,eq⟩
    let x : D := ⟨_,hx⟩
    let y : E := ⟨_,hy⟩
    refine ⟨x,y,rfl,rfl,cartesianEquiv D E (x,y),?_,rfl⟩
    exact (congrArg (· ∘ finSumFinEquiv.symm) eta).trans eq

theorem pieceClass_degree_zero (a : Fin 0 → V) (h : A.Definable J {a}) :
    pieceClass {a} h = 1 := by
  apply relation_sound
  apply Relation.one
  let e := singlePoints h
  exact ⟨e.unique⟩

theorem pieceClass_empty : pieceClass (∅ : Set (Fin k → V)) (Set.definable_empty (A := A) (L := J)) = 0 := by
  apply relation_sound; apply Relation.empty
  exact ⟨fun t => (singlePoints (Set.definable_empty (A := A) (L := J))) t |>.property⟩

theorem pieceClass_cut {D E : Set (Fin k → V)} (hd : A.Definable J D) (he : A.Definable J E)
    (disj : Disjoint D E) :
    pieceClass (D ∪ E) (hd.union he) = pieceClass D hd + pieceClass E he := by
  classical
  let cut := Equiv.Set.union disj
  let e := ((singlePoints (hd.union he)).trans cut).trans
    (Equiv.sumCongr (singlePoints hd).symm (singlePoints he).symm)
  apply relation_sound; apply Relation.cut
  refine ⟨e,?_,?_⟩
  · intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    convert graph_of_map id (fun i => Set.DefinableFun.proj J) D hd using 1
    ext w; constructor
    · rintro ⟨x,hx,y,hy,eq⟩
      have back := (e.symm_apply_apply ⟨0,x⟩).symm.trans (congrArg e.symm eq)
      have same := congrArg (fun t => ((singlePoints (hd.union he)) t).val) back
      change x.val = y.val at same
      exact ⟨hx ▸ same.symm ▸ y.property,hx ▸ hy ▸ same⟩
    · rintro ⟨hx,eq⟩
      let y : D := ⟨_,hx⟩
      let t := e.symm (.inl ⟨0,y⟩)
      exact ⟨t.2,rfl,y,eq,e.apply_symm_apply _⟩
  · intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    convert graph_of_map id (fun i => Set.DefinableFun.proj J) E he using 1
    ext w; constructor
    · rintro ⟨x,hx,y,hy,eq⟩
      have back := (e.symm_apply_apply ⟨0,x⟩).symm.trans (congrArg e.symm eq)
      have same := congrArg (fun t => ((singlePoints (hd.union he)) t).val) back
      change x.val = y.val at same
      exact ⟨hx ▸ same.symm ▸ y.property,hx ▸ hy ▸ same⟩
    · rintro ⟨hx,eq⟩
      let y : E := ⟨_,hx⟩
      let t := e.symm (.inr ⟨0,y⟩)
      exact ⟨t.2,rfl,y,eq,e.apply_symm_apply _⟩

theorem pieceClass_partition {I : Type} [Fintype I] (D : I → Set (Fin k → V))
    (hd : ∀ i, A.Definable J (D i)) (disj : Pairwise (fun i j => Disjoint (D i) (D j))) :
    pieceClass (⋃ i, D i) (Set.definable_iUnion_of_finite hd) = ∑ i, pieceClass (D i) (hd i) :=
  (finite_scissor_sum (fun s h => pieceClass s h) Set.definable_empty pieceClass_empty
    (fun ha hb => ha.union hb) (fun _ _ => pieceClass_cut) D hd disj).choose_spec

end ValueObject
end GeneralizedEuler.Section4
