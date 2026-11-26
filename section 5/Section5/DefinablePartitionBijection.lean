module

public import Section5.DefinableRelations

/-! Glue a finite collection of definable bijections in common ambient
variables along matching partitions. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {V W : TCsort → Type} {I : Type} [Finite I]
  {A : Set (SortedAssignment X V)} {B : Set (SortedAssignment X W)}

/-- Piecewise bijections are realized by the union of their defining
graphs. Both partitions use the same finite index set. -/
theorem definable_bijection_of_partitions
    (D : I → Set (SortedAssignment X V)) (C : I → Set (SortedAssignment X W))
    (subD : ∀ i, D i ⊆ A) (subC : ∀ i, C i ⊆ B)
    (disjD : Pairwise (fun i j => Disjoint (D i) (D j)))
    (disjC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (coverD : ∀ a ∈ A, ∃ i, a ∈ D i) (coverC : ∀ b ∈ B, ∃ i, b ∈ C i)
    (e : ∀ i, D i ≃ C i)
    (h : ∀ i, DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ D i, (e i ⟨a,ha⟩).val = b)) :
    ∃ f : A ≃ B, DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ A, (f ⟨a,ha⟩).val = b) := by
  classical
  let i (a : A) : I := (coverD a.val a.property).choose
  have ha (a : A) : a.val ∈ D (i a) := (coverD a.val a.property).choose_spec
  let f (a : A) : B := ⟨(e (i a) ⟨a.val,ha a⟩).val,subC (i a) (e (i a) ⟨a.val,ha a⟩).property⟩
  have use (j : I) (a : A) (haj : a.val ∈ D j) : (f a).val = (e j ⟨a.val,haj⟩).val := by
    have eq : j = i a := by
      by_contra hn
      exact Set.disjoint_left.1 (disjD hn) haj (ha a)
    subst j
    rfl
  have bij : Function.Bijective f := by
    constructor
    · intro a b eq
      have he : i b = i a := by
        by_contra hn
        have same := congrArg Subtype.val eq
        exact Set.disjoint_left.1 (disjC hn)
          (same.symm ▸ show (f b).val ∈ C (i b) from (e (i b) ⟨b.val,ha b⟩).property)
          (show (f a).val ∈ C (i a) from (e (i a) ⟨a.val,ha a⟩).property)
      have hb : b.val ∈ D (i a) := he ▸ ha b
      apply Subtype.ext
      have ea : (e (i a) ⟨a.val,ha a⟩).val = (e (i a) ⟨b.val,hb⟩).val :=
        (congrArg Subtype.val eq).trans (use (i a) b hb)
      exact congrArg (fun x : D (i a) => x.val) ((e (i a)).injective (Subtype.ext ea))
    · intro b
      obtain ⟨j,hb⟩ := coverC b.val b.property
      let a := (e j).symm ⟨b.val,hb⟩
      let av : A := ⟨a.val,subD j a.property⟩
      refine ⟨av,Subtype.ext ((use j av a.property).trans ?_)⟩
      exact congrArg Subtype.val ((e j).apply_symm_apply ⟨b.val,hb⟩)
  refine ⟨Equiv.ofBijective f bij,?_⟩
  let G (j : I) : Set (SortedAssignment X (SumVariables V W)) := {w |
    ∃ ha : (fun s => w s ∘ Sum.inl) ∈ D j, (e j ⟨fun s => w s ∘ Sum.inl,ha⟩).val =
      (fun s => w s ∘ Sum.inr)}
  have gDef (j : I) : SortedDefinableOver M S.carrier (G j) := h j
  unfold DefinableRelation
  convert SortedDefinableOver.iUnion gDef using 1
  ext w
  let a : SortedAssignment X V := fun s => w s ∘ Sum.inl
  let b : SortedAssignment X W := fun s => w s ∘ Sum.inr
  change (∃ ha : a ∈ A, (f ⟨a,ha⟩).val = b) ↔ w ∈ ⋃ j, G j
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨ha,eq⟩
    let x : A := ⟨a,ha⟩
    exact ⟨i x,_,eq⟩
  · rintro ⟨j,haj,eq⟩
    exact ⟨subD j haj,(use j ⟨a,subD j haj⟩ haj).trans eq⟩

end GeneralizedEuler.Section5
