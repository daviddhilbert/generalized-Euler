module

public import Section4.DegreeZeroInclusion
public import Section4.UnaryFiberMatching
import all Section4.DegreeZeroInclusion
import all Section4.Factors
import all Section4.ValueScissors

/-! Complete a tagged whole-fiber matching by matching the remaining
individual labels over the fixed base. Their number is detected by the
Euler characteristic of their positive residue fibers. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
set_option backward.isDefEq.respectTransparency false
open FirstOrder ValueObject
variable {V : Type*} {J : Language} [J.Structure V] {A : Set V} {k : ℕ}
  (U W : Over (J := J) A k)

def pointTuple (p : U.points A) : Fin k → V := p.2.val

def taggedGraph (R : U.points A → W.points A → Prop) (i : Fin U.tags) (j : Fin W.tags) :
    Set (Fin k ⊕ Fin k → V) :=
  {w | ∃ x : U.piece i, x.val = w ∘ Sum.inl ∧ ∃ y : W.piece j, y.val = w ∘ Sum.inr ∧ R ⟨i,x⟩ ⟨j,y⟩}

private theorem taggedGraph_or (R Q : U.points A → W.points A → Prop) (i j) :
    taggedGraph U W (fun x y => R x y ∨ Q x y) i j = taggedGraph U W R i j ∪ taggedGraph U W Q i j := by
  ext w; constructor
  · rintro ⟨x,hx,y,hy,h|h⟩
    exacts [Or.inl ⟨x,hx,y,hy,h⟩,Or.inr ⟨x,hx,y,hy,h⟩]
  · rintro (⟨x,hx,y,hy,h⟩|⟨x,hx,y,hy,h⟩)
    exacts [⟨x,hx,y,hy,Or.inl h⟩,⟨x,hx,y,hy,Or.inr h⟩]

private theorem taggedSingleton (p : U.points A) (q : W.points A)
    (hp : A.Definable J {p.2.val}) (hq : A.Definable J {q.2.val}) (i j) :
    A.Definable J (taggedGraph U W (fun x y => x=p ∧ y=q) i j) := by
  classical
  obtain ⟨t,p⟩ := p
  obtain ⟨s,q⟩ := q
  by_cases hi : i=t
  · subst t; by_cases hj : j=s
    · subst s
      convert (hp.preimage_comp Sum.inl).inter (hq.preimage_comp Sum.inr) using 1
      ext w
      exact ⟨fun ⟨x,hx,y,hy,h1,h2⟩ => by cases h1; cases h2; exact ⟨hx.symm,hy.symm⟩,
        fun h => ⟨p,h.1.symm,q,h.2.symm,rfl,rfl⟩⟩
    · have eq : taggedGraph U W (fun x y => x=⟨i,p⟩ ∧ y=⟨s,q⟩) i j = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨_,_,_,_,_,h⟩ => hj (congrArg Sigma.fst h)
      rw [eq]; exact Set.definable_empty
  · have eq : taggedGraph U W (fun x y => x=⟨t,p⟩ ∧ y=⟨s,q⟩) i j = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨_,_,_,_,h,_⟩ => hi (congrArg Sigma.fst h)
    rw [eq]; exact Set.definable_empty

theorem complete_tagged_matching (D : Set (U.points A)) (E : Set (W.points A)) (g : D ≃ E)
    (hg : ∀ i j, A.Definable J (taggedGraph U W (fun x y => ∃ a : D, a.val=x ∧ (g a).val=y) i j))
    (fd : Dᶜ.Finite) (fe : Eᶜ.Finite)
    (du : ∀ a : (Dᶜ : Set _), A.Definable J {pointTuple U a.val})
    (dw : ∀ b : (Eᶜ : Set _), A.Definable J {pointTuple W b.val})
    (euler : -(Nat.card (Dᶜ : Set _) : ℤ) = -(Nat.card (Eᶜ : Set _) : ℤ)) :
    taggedValueClass A U = taggedValueClass A W := by
  classical
  let : Fintype (Dᶜ : Set _) := fd.fintype
  let : Fintype (Eᶜ : Set _) := fe.fintype
  have eq : Fintype.card (Dᶜ : Set _) = Fintype.card (Eᶜ : Set _) := by
    simpa only [neg_inj,Nat.cast_inj,Nat.card_eq_fintype_card] using euler
  let f := Fintype.equivOfCardEq eq
  let all := (Equiv.Set.sumCompl D).symm.trans ((Equiv.sumCongr g f).trans (Equiv.Set.sumCompl E))
  let R (x : U.points A) (y : W.points A) := ∃ a : D, a.val=x ∧ (g a).val=y
  let Q (x : U.points A) (y : W.points A) := ∃ a : (Dᶜ : Set _), x=a.val ∧ y=(f a).val
  have graph : (fun x y => all x = y) = fun x y => R x y ∨ Q x y := by
    funext x y; apply propext
    constructor
    · rintro rfl
      by_cases h : x ∈ D
      · left; exact ⟨⟨x,h⟩,rfl,by simp [all,Equiv.Set.sumCompl_symm_apply_of_mem h]⟩
      · right; exact ⟨⟨x,h⟩,rfl,by simp [all,Equiv.Set.sumCompl_symm_apply_of_notMem h]⟩
    · rintro (⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩) <;> simp [all]
  apply relation_sound (Relation.iso U W ⟨all,?_⟩)
  intro i j
  change A.Definable J (taggedGraph U W (fun x y => all x = y) i j)
  rw [graph,taggedGraph_or]
  apply (hg i j).union
  have eqQ : taggedGraph U W Q i j = ⋃ a : (Dᶜ : Set _), taggedGraph U W (fun x y => x=a.val ∧ y=(f a).val) i j := by
    ext w; rw [Set.mem_iUnion]
    exact ⟨fun ⟨x,hx,y,hy,a,ha,hb⟩ => ⟨a,x,hx,y,hy,ha,hb⟩,fun ⟨a,x,hx,y,hy,ha,hb⟩ => ⟨x,hx,y,hy,a,ha,hb⟩⟩
  rw [eqQ]
  exact Set.definable_iUnion_of_finite (fun a => taggedSingleton U W a.val (f a).val (du a) (dw _) i j)

end GeneralizedEuler.Section4
