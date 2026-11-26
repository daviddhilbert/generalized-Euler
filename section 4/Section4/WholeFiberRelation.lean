module

public import Section4.FiniteScissors
public import Section4.MatchingRectangles
public import Section4.CellProducts

/-! Whole-fiber matching is definable over the parameters of a graph and
of the two families it relates. All value labels may be represented in RV. -/
public section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
  {M : SortedStructure L E Z} {S : SortedSubstructure M}

theorem isRVSet_project {I J : Type} [Finite J] {D : Set (I ⊕ J → Z .rv)}
    (h : isRVSet M S D) : isRVSet M S {x | ∃ y : J → Z .rv, Sum.elim x y ∈ D} := by
  let V := RVVariables I
  let r : ∀ s, RVVariables (I ⊕ J) s → AddRVCoordinates V J s
    | .vf => PEmpty.elim
    | .rv => id
  exact SortedDefinableOver.project_rv_coordinates (h.pullback_relabel r)

theorem isRVSet_forall {I J : Type} [Finite J] {D : Set (I ⊕ J → Z .rv)}
    (h : isRVSet M S D) : isRVSet M S {x | ∀ y : J → Z .rv, Sum.elim x y ∈ D} := by
  have hc : isRVSet M S Dᶜ := h.compl
  have hn := (isRVSet_project hc).compl
  unfold isRVSet
  convert hn using 1
  ext x; simp

/-- The image of one source fiber under the graph is the whole target
fiber. The formula includes every target representative. -/
theorem definable_whole_fiber {I X Y : Type} [Finite X] [Finite Y]
    (A : (I → Z .rv) → (X → Z .rv) → Prop) (B : (I → Z .rv) → (Y → Z .rv) → Prop)
    (R : (X → Z .rv) → (Y → Z .rv) → Prop)
    (ha : isRVSet M S {t : I ⊕ X → Z .rv | A (t ∘ Sum.inl) (t ∘ Sum.inr)})
    (hb : isRVSet M S {t : I ⊕ Y → Z .rv | B (t ∘ Sum.inl) (t ∘ Sum.inr)})
    (hr : isRVSet M S {t : X ⊕ Y → Z .rv | R (t ∘ Sum.inl) (t ∘ Sum.inr)}) :
    isRVSet M S {i | ∀ y, B i y ↔ ∃ x, A i x ∧ R x y} := by
  let ra : I ⊕ X → (I ⊕ Y) ⊕ X := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let rr : X ⊕ Y → (I ⊕ Y) ⊕ X := Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  let F : Set (I ⊕ Y → Z .rv) := {t | ∃ x, A (t ∘ Sum.inl) x ∧ R x (t ∘ Sum.inr)}
  have hf : isRVSet M S F := isRVSet_project (isRVSet_inter (isRVSet_precomp ra ha) (isRVSet_precomp rr hr))
  let D : Set (I ⊕ Y → Z .rv) := {t | B (t ∘ Sum.inl) (t ∘ Sum.inr) ↔ t ∈ F}
  have hd : isRVSet M S D := by
    let good := (hb.inter hf).union (hb.compl.inter hf.compl)
    unfold isRVSet
    convert good using 1
    ext t
    change (_ ↔ _) ↔ (_ ∧ _) ∨ (¬_ ∧ ¬_)
    tauto
  exact isRVSet_forall hd

/-- A separated graph of whole-fiber matches is a finite disjoint family
of graphs of Cartesian products of partial bijections. Empty rectangles
may be dropped, including when the entire relation is empty. -/
theorem decompose_matching_graph {A B C D : Type*}
    {P : Set (A × B) → Prop} {Q : Set (C × D) → Prop}
    (pu : P Set.univ) (pi : ∀ {s t}, P s → P t → P (s ∩ t))
    (pc : ∀ {s}, P s → P sᶜ) (qe : Q ∅) (qu : ∀ {s t}, Q s → Q t → Q (s ∪ t))
    (R : Set ((A × B) × (C × D))) (sep : SeparatedSets P Q R)
    (single : ∀ {a b b' c d d'}, ((a,b),c,d) ∈ R → ((a,b'),c,d') ∈ R → b = b' ∧ d = d')
    (inj : ∀ {a a' b c c' d}, ((a,b),c,d) ∈ R → ((a',b),c',d) ∈ R → a = a' ∧ c = c') :
    ∃ (l : ℕ) (U : Fin l → Set (A × B)) (V : Fin l → Set (C × D)),
      (∀ i, P (U i) ∧ Q (V i)) ∧ R = ⋃ i, U i ×ˢ V i ∧
      Pairwise (fun i j => Disjoint (U i ×ˢ V i) (U j ×ˢ V j)) ∧
      ∀ i, ∃ (p : {a // ∃ b, (a,b) ∈ U i} ≃ {b // ∃ a, (a,b) ∈ U i})
        (η : {c // ∃ d, (c,d) ∈ V i} ≃ {d // ∃ c, (c,d) ∈ V i}),
        ∀ a c b d, (a.val,b.val) ∈ U i ∧ (c.val,d.val) ∈ V i ↔ p a = b ∧ η c = d := by
  classical
  obtain ⟨l,U,V,hDef,unique,cell⟩ := separated_partition pu pi pc qe qu sep
  let I := {i : Fin l // (U i).Nonempty ∧ (V i).Nonempty}
  let e := (Fintype.equivFin I).symm
  let idx (i : Fin (Fintype.card I)) := (e i).val
  have belong {i a b c d} (hu : (a,b) ∈ U i) (hv : (c,d) ∈ V i) :
      ((a,b),c,d) ∈ R := (cell _ _ i hu).mpr hv
  refine ⟨_,U ∘ idx,V ∘ idx,fun i => hDef _,?_,?_,?_⟩
  · ext x
    obtain ⟨⟨a,b⟩,c,d⟩ := x
    rw [Set.mem_iUnion]; constructor
    · intro hx
      obtain ⟨i,hi,_⟩ := unique (a,b)
      have hv := (cell _ _ i hi).mp hx
      let j : I := ⟨i,⟨_,hi⟩,⟨_,hv⟩⟩
      exact ⟨e.symm j,by simpa [idx,j] using And.intro hi hv⟩
    · rintro ⟨i,hi⟩; exact belong hi.1 hi.2
  · intro i j neq
    apply Set.disjoint_left.mpr
    rintro ⟨x,y⟩ hi hj
    obtain ⟨k,_,uniq⟩ := unique x
    exact neq (e.injective (Subtype.ext ((uniq _ hi.1).trans (uniq _ hj.1).symm)))
  · intro i
    have hu := (e i).property.1
    have hv := (e i).property.2
    exact factor_matching_rectangle (fun a b => (a,b) ∈ U (idx i)) (fun c d => (c,d) ∈ V (idx i))
      (by obtain ⟨⟨x,y⟩,h⟩ := hu; exact ⟨x,y,h⟩) (by obtain ⟨⟨x,y⟩,h⟩ := hv; exact ⟨x,y,h⟩)
      (fun h h' k k' => single (belong h h') (belong k k'))
      (fun h h' k k' => inj (belong h h') (belong k k'))

end GeneralizedEuler.Section4
