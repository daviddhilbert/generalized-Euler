module

public import Section5.MixedTaggedEquivalence

/-! Each entry of a tagged graph gives an isomorphism of definable
cuts. Rows partition the source pieces and columns partition the targets. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5.MixedTaggedFamily

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  (A B : MixedTaggedFamily M S) (f : A.Points ≃ B.Points)

@[expose] def sourceCut (i : A.Tag) (j : B.Tag) : Set (SortedAssignment X (A.coordinates i)) :=
  {x | ∃ y, A.graphOver B f i j x y}

@[expose] def targetCut (i : A.Tag) (j : B.Tag) : Set (SortedAssignment X (B.coordinates j)) :=
  {y | ∃ x, A.graphOver B f i j x y}

theorem sourceCut_subset (i : A.Tag) (j : B.Tag) : A.sourceCut B f i j ⊆ A.piece i :=
  fun _ ⟨_,hx,_,_⟩ => hx

theorem targetCut_subset (i : A.Tag) (j : B.Tag) : A.targetCut B f i j ⊆ B.piece j :=
  fun _ ⟨_,_,hy,_⟩ => hy

theorem sourceCut_definable (d : A.HasDefinableGraph B f) (i : A.Tag) (j : B.Tag) :
    SortedDefinableOver M S.carrier (A.sourceCut B f i j) := by
  convert (d i j).transpose.image (B.definable j) using 1
  ext x
  constructor
  · rintro ⟨y,hx,hy,eq⟩
    exact ⟨y,hy,hx,hy,eq⟩
  · rintro ⟨y,_,h⟩
    exact ⟨y,h⟩

theorem targetCut_definable (d : A.HasDefinableGraph B f) (i : A.Tag) (j : B.Tag) :
    SortedDefinableOver M S.carrier (A.targetCut B f i j) := by
  convert (d i j).image (A.definable i) using 1
  ext y
  constructor
  · rintro ⟨x,hx,hy,eq⟩
    exact ⟨x,hx,hx,hy,eq⟩
  · rintro ⟨x,_,h⟩
    exact ⟨x,h⟩

theorem sourceCut_partition (i : A.Tag) :
    Pairwise (fun j k => Disjoint (A.sourceCut B f i j) (A.sourceCut B f i k)) ∧
    (⋃ j, A.sourceCut B f i j) = A.piece i := by
  constructor
  · intro j k ne
    apply Set.disjoint_left.2
    rintro x ⟨y,hx,hy,e⟩ ⟨z,hx',hz,e'⟩
    exact ne (congrArg Sigma.fst (e.symm.trans e'))
  · ext x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := Set.mem_iUnion.1 hx
      exact A.sourceCut_subset B f i j hj
    · intro hx
      let y := f ⟨i,⟨x,hx⟩⟩
      exact Set.mem_iUnion.2 ⟨y.1,y.2.val,hx,y.2.property,rfl⟩

theorem targetCut_partition (j : B.Tag) :
    Pairwise (fun i k => Disjoint (A.targetCut B f i j) (A.targetCut B f k j)) ∧
    (⋃ i, A.targetCut B f i j) = B.piece j := by
  constructor
  · intro i k ne
    apply Set.disjoint_left.2
    rintro y ⟨x,hx,hy,e⟩ ⟨z,hz,hy',e'⟩
    exact ne (congrArg Sigma.fst (f.injective (e.trans e'.symm)))
  · ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := Set.mem_iUnion.1 hy
      exact A.targetCut_subset B f i j hi
    · intro hy
      let x := f.symm ⟨j,⟨y,hy⟩⟩
      exact Set.mem_iUnion.2 ⟨x.1,x.2.val,x.2.property,hy,f.apply_symm_apply _⟩

private theorem sameTag_val_eq (C : MixedTaggedFamily M S) (k : C.Tag) {x y : C.piece k}
    (h : (⟨k,x⟩ : C.Points) = ⟨k,y⟩) : x.val = y.val :=
  congrArg (fun a : C.piece k => a.val) (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

theorem cuts_iso (d : A.HasDefinableGraph B f) (i : A.Tag) (j : B.Tag) :
    Nonempty (MixedGraphIso M S (A.sourceCut B f i j) (A.targetCut B f i j)) := by
  classical
  let P := A.sourceCut B f i j
  let Q := A.targetCut B f i j
  have image (x : P) : ∃ y : Q, A.graphOver B f i j x.val y.val := by
    obtain ⟨y,h⟩ := x.property
    exact ⟨⟨y,x.val,h⟩,h⟩
  let g (x : P) : Q := (image x).choose
  have graph (x : P) : A.graphOver B f i j x.val (g x).val := (image x).choose_spec
  have bij : Function.Bijective g := by
    constructor
    · intro a b e
      obtain ⟨ha,hy,ea⟩ := graph a
      obtain ⟨hb,hy',eb⟩ := graph b
      have ev := congrArg (fun y : Q => y.val) e
      have tags : (⟨j,⟨(g a).val,hy⟩⟩ : B.Points) = ⟨j,⟨(g b).val,hy'⟩⟩ :=
        Sigma.ext rfl (heq_of_eq (Subtype.ext ev))
      exact Subtype.ext (sameTag_val_eq A i (f.injective (ea.trans (tags.trans eb.symm))))
    · intro b
      obtain ⟨x,hx,hy,e⟩ := b.property
      let a : P := ⟨x,b.val,hx,hy,e⟩
      obtain ⟨_,_,ea⟩ := graph a
      have h := ea.symm.trans e
      exact ⟨a,Subtype.ext (sameTag_val_eq B j h)⟩
  refine ⟨⟨Equiv.ofBijective g bij,(d i j).congr ?_⟩⟩
  intro x y
  constructor
  · rintro ⟨hx,hy,e⟩
    let a : P := ⟨x,y,hx,hy,e⟩
    obtain ⟨_,_,ea⟩ := graph a
    have h := ea.symm.trans e
    exact ⟨a.property,sameTag_val_eq B j h⟩
  · rintro ⟨hx,rfl⟩
    exact graph ⟨x,hx⟩

end GeneralizedEuler.Section5.MixedTaggedFamily
