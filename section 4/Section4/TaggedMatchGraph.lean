module

public import Section4.TaggedLiftRealization
public import Section4.UnaryTaggedComparison
import all Section4.RVTaggedEquivalence
import all Section4.ValuePullback
import all Section4.UnaryFiberMatching
import all Section4.UnaryTaggedComparison
import all Section4.Factors

/-! Definability of the value-label graph of a tagged bijection on lifts.
Both directions are tested on a pair of tags so that a fiber cannot split
across different target tags. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {I X Y : Type} [Finite X] [Finite Y]

private theorem definable_fiber_cover (A : (I → Z .rv) → (X → Z .rv) → Prop)
    (B : (I → Z .rv) → (Y → Z .rv) → Prop) (R : (X → Z .rv) → (Y → Z .rv) → Prop)
    (ha : isRVSet M S {p : I ⊕ X → Z .rv | A (p ∘ Sum.inl) (p ∘ Sum.inr)})
    (hb : isRVSet M S {p : I ⊕ Y → Z .rv | B (p ∘ Sum.inl) (p ∘ Sum.inr)})
    (hr : isRVSet M S {p : X ⊕ Y → Z .rv | R (p ∘ Sum.inl) (p ∘ Sum.inr)}) :
    isRVSet M S {p | ∀ x, A p x → ∃ y, B p y ∧ R x y} := by
  let rb : I ⊕ Y → (I ⊕ X) ⊕ Y := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let rr : X ⊕ Y → (I ⊕ X) ⊕ Y := Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
  let E := {p : I ⊕ X → Z .rv | ∃ y, B (p ∘ Sum.inl) y ∧ R (p ∘ Sum.inr) y}
  have he : isRVSet M S E := isRVSet_project (isRVSet_inter (isRVSet_precomp rb hb) (isRVSet_precomp rr hr))
  let D := {p : I ⊕ X → Z .rv | A (p ∘ Sum.inl) (p ∘ Sum.inr) → p ∈ E}
  have hd : isRVSet M S D := by
    unfold isRVSet
    convert ha.compl.union he using 1
    ext p; change (_ → _) ↔ ¬_ ∨ _; tauto
  exact isRVSet_forall hd

variable {Γ : Type*} {J : Language} [J.Structure Γ] (v : Z .rv → Γ) (A : Set Γ)
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  {k : ℕ} (U W : Over (J := J) A k)

def sharpLabel (x : (taggedSharp v A defSharp U).Points) : U.points A :=
  ⟨x.1,v ∘ x.2.val,x.2.property.2⟩

abbrev rvZero := M.funMap .rvZero (fun i => i.elim0)

def tupleSharp (I : Type) (D : Set (I → Γ)) : Set (I → Z .rv) :=
  {x | (∀ i, x i ≠ rvZero (M := M)) ∧ v ∘ x ∈ D}

variable (f : (taggedSharp v A defSharp U).Points ≃ (taggedSharp v A defSharp W).Points)
  (graph : ∀ i j, isRVSet M S (RVFamily.graphPiece _ _ f i j))

include graph in
theorem tagged_match_graph_definable
    (reflect : ∀ D : Set (Fin k ⊕ Fin k → Γ), isRVSet M S (tupleSharp (M := M) v _ D) → A.Definable J D)
    (fiberDef : isRVSet M S {p : Fin k ⊕ Fin k → Z .rv |
      (∀ i, p (.inr i) ≠ rvZero (M := M)) ∧ v ∘ p ∘ Sum.inr = v ∘ p ∘ Sum.inl})
    (i : Fin U.tags) (j : Fin W.tags) :
    A.Definable J (taggedGraph U W (WholeMatch (sharpLabel v A defSharp U) (sharpLabel v A defSharp W) f) i j) := by
  let K := Fin k
  let P := K ⊕ K
  let Fa (p : P → Z .rv) (x : K → Z .rv) := (∀ n, x n ≠ rvZero (M := M)) ∧ v ∘ x = v ∘ p ∘ Sum.inl
  let Fb (p : P → Z .rv) (y : K → Z .rv) := (∀ n, y n ≠ rvZero (M := M)) ∧ v ∘ y = v ∘ p ∘ Sum.inr
  let R (x y : K → Z .rv) := Sum.elim x y ∈ RVFamily.graphPiece _ _ f i j
  have fa : isRVSet M S {w : P ⊕ K → Z .rv | Fa (w ∘ Sum.inl) (w ∘ Sum.inr)} :=
    isRVSet_precomp (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) fiberDef
  have fb : isRVSet M S {w : P ⊕ K → Z .rv | Fb (w ∘ Sum.inl) (w ∘ Sum.inr)} :=
    isRVSet_precomp (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr) fiberDef
  have rg : isRVSet M S {w : K ⊕ K → Z .rv | R (w ∘ Sum.inl) (w ∘ Sum.inr)} := by
    apply (show {w : K ⊕ K → Z .rv | R (w ∘ Sum.inl) (w ∘ Sum.inr)} = RVFamily.graphPiece _ _ f i j from ?_).symm ▸ graph i j
    apply Set.ext; intro w
    exact (congrArg (· ∈ RVFamily.graphPiece _ _ f i j) (show Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w from funext (Sum.rec (fun _ => rfl) (fun _ => rfl)))).to_iff
  have lr := definable_fiber_cover Fa Fb R fa fb rg
  have rl := definable_fiber_cover Fb Fa (fun y x => R x y) fb fa (isRVSet_precomp Sum.swap rg)
  have valid := isRVSet_inter (isRVSet_precomp Sum.inl (defSharp (U.isDefinable i)))
    (isRVSet_precomp Sum.inr (defSharp (W.isDefinable j)))
  apply reflect
  let covers := {p : P → Z .rv | (p ∘ Sum.inl ∈ sharp M v (U.piece i) ∧ p ∘ Sum.inr ∈ sharp M v (W.piece j)) ∧
    (∀ x, Fa p x → ∃ y, Fb p y ∧ R x y) ∧ (∀ y, Fb p y → ∃ x, Fa p x ∧ R x y)}
  have dc : isRVSet M S covers := isRVSet_inter valid (isRVSet_inter lr rl)
  refine (show tupleSharp (M := M) v _ _ = covers from ?_).symm ▸ dc
  apply Set.ext; intro p
  have rel {x y : K → Z .rv} (hx : x ∈ sharp M v (U.piece i)) (hy : y ∈ sharp M v (W.piece j)) :
      R x y ↔ f ⟨i,x,hx⟩ = ⟨j,y,hy⟩ := by
    constructor
    · rintro ⟨a,b,l,r,h⟩
      have l' : a=⟨x,hx⟩ := Subtype.ext l
      have r' : b=⟨y,hy⟩ := Subtype.ext r
      exact l' ▸ r' ▸ h
    · exact fun h => ⟨⟨x,hx⟩,⟨y,hy⟩,rfl,rfl,h⟩
  constructor
  · rintro ⟨nz,a,ha,b,hb,whole⟩
    have ua : v ∘ p ∘ Sum.inl ∈ U.piece i := ha ▸ a.property
    have wb : v ∘ p ∘ Sum.inr ∈ W.piece j := hb ▸ b.property
    refine ⟨⟨⟨fun n => nz (.inl n),ua⟩,⟨fun n => nz (.inr n),wb⟩⟩,?_,?_⟩
    · rintro x ⟨nx,eq⟩
      let t : (taggedSharp v A defSharp U).Points := ⟨i,x,nx,eq.symm ▸ ua⟩
      have mem : sharpLabel v A defSharp U t = ⟨i,a⟩ := Sigma.ext rfl (heq_of_eq (Subtype.ext (eq.trans ha.symm)))
      have out : sharpLabel v A defSharp W (f t) = ⟨j,b⟩ := (congrArg (f t ∈ ·) whole).mp ⟨t,mem,rfl⟩
      generalize h : f t = w at out
      obtain ⟨l,y⟩ := w
      obtain rfl : l=j := congrArg Sigma.fst out
      have e : v ∘ y.val = b.val := congrArg Subtype.val (Sigma.mk.inj_iff.mp out).2.eq
      exact ⟨y.val,⟨y.property.1,e.trans hb⟩,(rel t.2.property y.property).mpr h⟩
    · rintro y ⟨ny,eq⟩
      let t : (taggedSharp v A defSharp W).Points := ⟨j,y,ny,eq.symm ▸ wb⟩
      have mem : sharpLabel v A defSharp W t = ⟨j,b⟩ := Sigma.ext rfl (heq_of_eq (Subtype.ext (eq.trans hb.symm)))
      obtain ⟨⟨l,z⟩,old,h⟩ := (congrArg (t ∈ ·) whole).mpr mem
      obtain rfl : l=i := congrArg Sigma.fst old
      have e : v ∘ z.val = a.val := congrArg Subtype.val (Sigma.mk.inj_iff.mp old).2.eq
      exact ⟨z.val,⟨z.property.1,e.trans ha⟩,(rel z.property t.2.property).mpr h⟩
  · rintro ⟨⟨⟨nu,du⟩,nw,dw⟩,forward,backward⟩
    refine ⟨Sum.rec nu nw,⟨_,du⟩,rfl,⟨_,dw⟩,rfl,?_⟩
    apply Set.ext; intro z
    constructor
    · rintro ⟨⟨s,x⟩,same,rfl⟩
      obtain rfl : s=i := congrArg Sigma.fst same
      have eq : v ∘ x.val = v ∘ p ∘ Sum.inl := congrArg Subtype.val (Sigma.mk.inj_iff.mp same).2.eq
      obtain ⟨y,⟨ny,ey⟩,h⟩ := forward x.val ⟨x.property.1,eq⟩
      have hr := (rel x.property ⟨ny,ey.symm ▸ dw⟩).mp h
      change sharpLabel v A defSharp W (f _) = _
      rw [hr]; exact Sigma.ext rfl (heq_of_eq (Subtype.ext ey))
    · obtain ⟨s,y⟩ := z
      intro same
      obtain rfl : s=j := congrArg Sigma.fst same
      have ey : v ∘ y.val = v ∘ p ∘ Sum.inr := congrArg Subtype.val (Sigma.mk.inj_iff.mp same).2.eq
      obtain ⟨x,⟨nx,ex⟩,h⟩ := backward y.val ⟨y.property.1,ey⟩
      exact ⟨⟨i,x,nx,ex.symm ▸ du⟩,Sigma.ext rfl (heq_of_eq (Subtype.ext ex)),(rel _ y.property).mp h⟩

end GeneralizedEuler.Section4
