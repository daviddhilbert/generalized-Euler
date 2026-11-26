module

public import Section4.ValueScissors

/-! Comparing finite tagged value sets by the graph on each pair of tags. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder
variable {V : Type*} {J : Language} [J.Structure V] {A : Set V} {k : ℕ}
  {T : Type*} [AddCommMonoid T]

abbrev ValueWeight (J : Language) {V : Type*} [J.Structure V] (A : Set V) (k : ℕ) (T : Type*) :=
  (D : Set (Fin k → V)) → A.Definable J D → T

def sliceGraph {I H : Type} (D : I → Set (Fin k → V)) (E : H → Set (Fin k → V))
    (e : (Σ i, D i) ≃ (Σ j, E j)) (i : I) (j : H) : Set (Fin k ⊕ Fin k → V) :=
  {w | ∃ x : D i, x.val = w ∘ Sum.inl ∧ ∃ y : E j, y.val = w ∘ Sum.inr ∧ e ⟨i,x⟩ = ⟨j,y⟩}

theorem compare_tags (weight : ValueWeight J A k T)
    (partition : ∀ {I : Type} [Fintype I] (D : Set (Fin k → V)) (hd : A.Definable J D)
      (d : I → Set (Fin k → V)) (hs : ∀ i, A.Definable J (d i)),
      Pairwise (fun i j => Disjoint (d i) (d j)) → (⋃ i, d i) = D → weight D hd = ∑ i, weight _ (hs i))
    (invariant : ∀ (D E : Set (Fin k → V)) (hd : A.Definable J D) (he : A.Definable J E)
      (e : D ≃ E), A.Definable J {w : Fin k ⊕ Fin k → V |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} → weight D hd = weight E he)
    {I H : Type} [Fintype I] [Fintype H] (D : I → Set (Fin k → V)) (E : H → Set (Fin k → V))
    (hd : ∀ i, A.Definable J (D i)) (he : ∀ j, A.Definable J (E j))
    (e : (Σ i, D i) ≃ (Σ j, E j)) (hg : ∀ i j, A.Definable J (sliceGraph D E e i j)) :
    ∑ i, weight _ (hd i) = ∑ j, weight _ (he j) := by
  classical
  let left (i : I) (j : H) := {x | ∃ t : D i, t.val = x ∧ (e ⟨i,t⟩).1 = j}
  let right (i : I) (j : H) := {y | ∃ t : E j, t.val = y ∧ (e.symm ⟨j,t⟩).1 = i}
  have hL i j : A.Definable J (left i j) := by
    convert (hg i j).image_comp Sum.inl using 1
    ext x; constructor
    · rintro ⟨t,rfl,tag⟩
      generalize ez : e ⟨i,t⟩ = z at tag
      rcases z with ⟨j',y⟩
      change j' = j at tag; subst j'
      exact ⟨Sum.elim t.val y.val,⟨t,rfl,y,rfl,ez⟩,rfl⟩
    · rintro ⟨w,⟨t,hx,y,_,eq⟩,rfl⟩
      exact ⟨t,hx,congrArg Sigma.fst eq⟩
  have hR i j : A.Definable J (right i j) := by
    convert (hg i j).image_comp Sum.inr using 1
    ext y; constructor
    · rintro ⟨u,rfl,tag⟩
      generalize ez : e.symm ⟨j,u⟩ = z at tag
      rcases z with ⟨i',x⟩
      change i' = i at tag; subst i'
      exact ⟨Sum.elim x.val u.val,⟨x,rfl,u,rfl,e.symm_apply_eq.mp ez |>.symm⟩,rfl⟩
    · rintro ⟨w,⟨x,_,y,hy,eq⟩,rfl⟩
      exact ⟨y,hy,congrArg Sigma.fst (e.symm_apply_eq.mpr eq.symm)⟩
  have row i : weight _ (hd i) = ∑ j, weight _ (hL i j) := by
    apply partition
    · intro a b ne; apply Set.disjoint_left.mpr
      rintro _ ⟨x,rfl,hx⟩ ⟨y,hy,hy'⟩
      cases Subtype.ext hy
      exact ne (hx.symm.trans hy')
    · ext x; rw [Set.mem_iUnion]
      exact ⟨fun ⟨_,t,ht,_⟩ => ht ▸ t.property,fun hx => ⟨_,⟨x,hx⟩,rfl,rfl⟩⟩
  have col j : weight _ (he j) = ∑ i, weight _ (hR i j) := by
    apply partition
    · intro a b ne; apply Set.disjoint_left.mpr
      rintro _ ⟨x,rfl,hx⟩ ⟨y,hy,hy'⟩
      cases Subtype.ext hy
      exact ne (hx.symm.trans hy')
    · ext y; rw [Set.mem_iUnion]
      exact ⟨fun ⟨_,t,ht,_⟩ => ht ▸ t.property,fun hy => ⟨_,⟨y,hy⟩,rfl,rfl⟩⟩
  have pair i j : weight _ (hL i j) = weight _ (hR i j) := by
    let graph := sliceGraph D E e i j
    have lproj : Set.BijOn (fun w => w ∘ Sum.inl) graph (left i j) := by
      refine ⟨?_,?_,?_⟩
      · rintro w ⟨t,ht,y,_,eq⟩; exact ⟨t,ht,congrArg Sigma.fst eq⟩
      · rintro w ⟨a,ha,b,hb,eq⟩ z ⟨c,hc,d,ht,eq'⟩ h
        have ac : a = c := Subtype.ext (ha.trans (h.trans hc.symm))
        subst c
        have bd := Sigma.mk.inj_iff.mp (eq.symm.trans eq')
        have same : b = d := eq_of_heq bd.2
        subst d
        exact funext fun x => by cases x with | inl u => exact congrFun h u | inr u => exact congrFun (hb.symm.trans ht) u
      · rintro _ ⟨t,rfl,tag⟩
        generalize ez : e ⟨i,t⟩ = z at tag
        rcases z with ⟨j',y⟩
        change j' = j at tag; subst j'
        exact ⟨Sum.elim t.val y.val,⟨t,rfl,y,rfl,ez⟩,rfl⟩
    have rproj : Set.BijOn (fun w => w ∘ Sum.inr) graph (right i j) := by
      refine ⟨?_,?_,?_⟩
      · rintro w ⟨x,_,y,hy,eq⟩; exact ⟨y,hy,congrArg Sigma.fst (e.symm_apply_eq.mpr eq.symm)⟩
      · rintro w ⟨a,ha,b,hb,eq⟩ z ⟨c,hc,d,ht,eq'⟩ h
        have bd : b = d := Subtype.ext (hb.trans (h.trans ht.symm))
        subst d
        have ac := Sigma.mk.inj_iff.mp (e.injective (eq.trans eq'.symm))
        have same : a = c := eq_of_heq ac.2
        subst c
        exact funext fun x => by cases x with | inl u => exact congrFun (ha.symm.trans hc) u | inr u => exact congrFun h u
      · rintro _ ⟨t,rfl,tag⟩
        generalize ez : e.symm ⟨j,t⟩ = z at tag
        rcases z with ⟨i',x⟩
        change i' = i at tag; subst i'
        exact ⟨Sum.elim x.val t.val,⟨x,rfl,t,rfl,(e.symm_apply_eq.mp ez).symm⟩,rfl⟩
    let el := lproj.equiv _
    let er := rproj.equiv _
    apply invariant _ _ _ _ (el.symm.trans er)
    convert hg i j using 1
    ext w; constructor
    · rintro ⟨a,ha,hb⟩
      obtain ⟨z,rfl⟩ := el.surjective a
      change (er (el.symm (el z))).val = _ at hb
      rw [el.symm_apply_apply] at hb
      have eq : z.val = w := funext fun x => by cases x with | inl i => exact congrFun ha i | inr j => exact congrFun hb j
      exact eq ▸ z.property
    · intro hw
      let z : graph := ⟨w,hw⟩
      exact ⟨el z,rfl,congrArg (fun a => (er a).val) (el.symm_apply_apply z)⟩
  simp_rw [row,col,pair]
  exact Finset.sum_comm

end GeneralizedEuler.Section4.ValueObject
