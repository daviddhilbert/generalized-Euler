module

public import Section4.RVTaggedEquivalence
public import Section5.DefinableProjection
import all Section4.RVTaggedEquivalence

/-! Cut each source and target tag of a definable bijection by the tag
on its other side. The cut pieces still have definable bijections. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  (A B : RVFamily M S) (e : A.Points ≃ B.Points)

@[expose] def sourceGraphCut (i : A.Tag) (j : B.Tag) : Set (A.Coord i → X .rv) :=
  {x | ∃ u : A.piece i, u.val = x ∧ (e ⟨i,u⟩).1 = j}

theorem sourceGraphCut_subset (i : A.Tag) (j : B.Tag) :
    sourceGraphCut A B e i j ⊆ A.piece i := by
  rintro x ⟨u,rfl,_⟩
  exact u.property

theorem sourceGraphCut_definable (i : A.Tag) (j : B.Tag)
    (graph : isRVSet M S (RVFamily.graphPiece A B e i j)) :
    isRVSet M S (sourceGraphCut A B e i j) := by
  convert isRVSet_project graph using 1
  ext x
  change (∃ u : A.piece i, u.val = x ∧ (e ⟨i,u⟩).1 = j) ↔
    ∃ y : B.Coord j → X .rv, Sum.elim x y ∈ RVFamily.graphPiece A B e i j
  constructor
  · rintro ⟨u,hu,h⟩
    generalize hE : e ⟨i,u⟩ = v at h ⊢
    obtain ⟨d,v⟩ := v
    change d = j at h
    subst d
    exact ⟨v.val,u,v,hu,rfl,hE⟩
  · rintro ⟨_,u,v,hu,_,he⟩
    exact ⟨u,hu,congrArg Sigma.fst he⟩

theorem sourceGraphCut_partition (i : A.Tag) :
    Pairwise (fun j l => Disjoint (sourceGraphCut A B e i j) (sourceGraphCut A B e i l)) ∧
      (⋃ j, sourceGraphCut A B e i j) = A.piece i := by
  constructor
  · intro j l ne
    apply Set.disjoint_left.2
    rintro x ⟨u,hu,hj⟩ ⟨v,hv,hl⟩
    have eq : u = v := Subtype.ext (hu.trans hv.symm)
    exact ne (hj.symm.trans (eq.symm ▸ hl))
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun j => sourceGraphCut_subset A B e i j
    · intro x hx
      let u : A.piece i := ⟨x,hx⟩
      exact Set.mem_iUnion.2 ⟨(e ⟨i,u⟩).1,u,rfl,rfl⟩

private theorem sourceGraphCut_match (i : A.Tag) (j : B.Tag)
    (x : sourceGraphCut A B e i j) :
    ∃ u : A.piece i, u.val = x.val ∧ ∃ v : B.piece j, e ⟨i,u⟩ = ⟨j,v⟩ := by
  obtain ⟨u,hx,he⟩ := x.property
  generalize hE : e ⟨i,u⟩ = y at he ⊢
  obtain ⟨d,v⟩ := y
  change d = j at he
  subst d
  exact ⟨u,hx,v,hE⟩

/-- A graph cut is isomorphic to the corresponding inverse-graph cut,
using the defining graph of the original bijection on this tag pair. -/
theorem sourceGraphCut_equivalent (i : A.Tag) (j : B.Tag)
    (graph : isRVSet M S (RVFamily.graphPiece A B e i j)) :
    RVDefinablyEquivalent M S.carrier (sourceGraphCut A B e i j) (sourceGraphCut B A e.symm j i) := by
  classical
  let D := sourceGraphCut A B e i j
  let C := sourceGraphCut B A e.symm j i
  choose u hu v hv using sourceGraphCut_match A B e i j
  let f (x : D) : C := ⟨(v x).val,v x,rfl,congrArg Sigma.fst ((e.symm_apply_eq).2 (hv x).symm)⟩
  have back (x : D) (a : A.piece i) (b : B.piece j) (ha : a.val = x.val)
      (he : e ⟨i,a⟩ = ⟨j,b⟩) : f x = ⟨b.val,b,rfl,congrArg Sigma.fst ((e.symm_apply_eq).2 he.symm)⟩ := by
    have same : u x = a := Subtype.ext ((hu x).trans ha.symm)
    have h : (⟨j,v x⟩ : B.Points) = ⟨j,b⟩ := (hv x).symm.trans (same ▸ he)
    exact Subtype.ext (congrArg (fun z : B.piece j => z.val) (Sigma.mk.inj_iff.mp h).2.eq)
  have bij : Function.Bijective f := by
    constructor
    · intro x y h
      have ev : v x = v y := Subtype.ext (congrArg (fun z : C => z.val) h)
      have p : (⟨i,u x⟩ : A.Points) = ⟨i,u y⟩ := e.injective ((hv x).trans (ev ▸ (hv y).symm))
      exact Subtype.ext ((hu x).symm.trans
        ((congrArg Subtype.val (Sigma.mk.inj_iff.mp p).2.eq).trans (hu y)))
    · intro y
      obtain ⟨b,hb,a,h⟩ := sourceGraphCut_match B A e.symm j i y
      have he := e.symm_apply_eq.1 h
      let x : D := ⟨a.val,a,rfl,congrArg Sigma.fst he.symm⟩
      exact ⟨x,(back x a b rfl he.symm).trans (Subtype.ext hb)⟩
  refine ⟨Equiv.ofBijective f bij,?_⟩
  have hgraph : SortedDefinableOver M S.carrier
      {w : SortedAssignment X (RVVariables (A.Coord i ⊕ B.Coord j)) |
        w .rv ∈ RVFamily.graphPiece A B e i j} := graph
  convert hgraph using 1
  ext w
  change (∃ x : D, x.val = w .rv ∘ Sum.inl ∧ (f x).val = w .rv ∘ Sum.inr) ↔
    w .rv ∈ RVFamily.graphPiece A B e i j
  constructor
  · rintro ⟨x,hx,hy⟩
    exact ⟨u x,v x,(hu x).trans hx,hy,hv x⟩
  · rintro ⟨a,b,ha,hb,he⟩
    let x : D := ⟨a.val,a,rfl,congrArg Sigma.fst he⟩
    exact ⟨x,ha,(congrArg Subtype.val (back x a b rfl he)).trans hb⟩

end GeneralizedEuler.Section5
