module

public import Section4.ValueMembershipPartition
public import Section4.HeightDrop
import all Section4.ValueStratification

/-! Cut the complement of finitely many matched rectangles into
residue pieces times disjoint affine value strata. Only nonempty
residue pieces are kept, so every remaining height strictly drops. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder
variable {F V X : Type*} [Field F] [AddCommGroup V] [Module F V] {J : Language} [J.Structure V]
  {G : Submodule F V} {n : ℕ} {I : Type} [Fintype I]

theorem rectangle_remainder_grid (lang : ValueLanguage (J := J) G)
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set V).Definable J D))
    {P : Set X → Prop} (U : Set X) (D : Set (Fin n → V)) (hd : (G : Set V).Definable J D)
    (A : I → Set X) (B : I → Set (Fin n → V)) (hb : ∀ i, (G : Set V).Definable J (B i))
    (cut : ∀ T : Finset I, P (U \ ⋃ i ∈ T, A i))
    (height : ℕ) (bound : n ≤ height)
    (independentCovered : n = height → ∀ u ∈ U, ∀ a ∈ D, LinearIndependent F (G.mkQ ∘ a) →
      ∃ i, u ∈ A i ∧ a ∈ B i) :
    ∃ (l : ℕ) (q : Fin l → DefinablePiece J G n) (R : Fin l → Set X),
      (∀ t, P (R t) ∧ (R t).Nonempty ∧ (q t).rank < height) ∧
      Pairwise (fun i j => Disjoint (q i).support (q j).support) ∧
      (U ×ˢ D) \ (⋃ i, A i ×ˢ B i) = ⋃ t, R t ×ˢ (q t).support := by
  classical
  let tests : Option I → Set (Fin n → V) := Option.elim' D B
  have defs : ∀ i, (G : Set V).Definable J (tests i) := fun i => by cases i with
    | none => exact hd
    | some i => exact hb i
  obtain ⟨l,p,active,unique,truth⟩ := stratify_memberships lang sat tests defs
  let chosen t := Finset.univ.filter (fun i => active t (some i) = true)
  let rest t := U \ ⋃ i ∈ chosen t, A i
  let K := {t : Fin l // active t none = true ∧ (rest t).Nonempty}
  let e := (Fintype.equivFin K).symm
  have remaining {t : Fin l} {u a} (hu : u ∈ rest t) (ha : a ∈ (p t).support) :
      (u,a) ∉ ⋃ i, A i ×ˢ B i := by
    intro h
    obtain ⟨i,ui,ai⟩ := Set.mem_iUnion.mp h
    have hit := (truth t (some i) a ha).mp ai
    exact hu.2 (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩,ui⟩⟩)
  have rank (t : K) : (p t.val).rank < height := by
    have le := Fintype.card_le_of_injective (p t.val).frame.free (p t.val).frame.free.injective
    simp only [Fintype.card_fin] at le
    by_cases top : n = height
    · rw [← top]
      apply no_independent_rank_drop (p t.val).frame (p t.val).domain (p t.val).independent
      intro a ha ind
      obtain ⟨u,hu⟩ := t.property.2
      have haD := (truth t.val none a ha).mpr t.property.1
      obtain ⟨i,h⟩ := independentCovered top u hu.1 a haD ind
      exact remaining hu ha (Set.mem_iUnion.mpr ⟨i,h⟩)
    · omega
  refine ⟨_,fun t => p (e t).val,fun t => rest (e t).val,fun t => ⟨cut _,(e t).property.2,rank _⟩,?_,?_⟩
  · intro i j ne
    apply Set.disjoint_left.mpr
    intro x hi hj
    obtain ⟨_,_,uniq⟩ := unique x
    exact ne (e.injective (Subtype.ext ((uniq _ hi).trans (uniq _ hj).symm)))
  · ext z
    obtain ⟨u,a⟩ := z
    constructor
    · rintro ⟨⟨hu,ha⟩,unmatched⟩
      obtain ⟨t,ht,_⟩ := unique a
      have ur : u ∈ rest t := by
        refine ⟨hu,?_⟩
        intro h
        obtain ⟨i,h⟩ := Set.mem_iUnion.mp h
        obtain ⟨sel,ui⟩ := Set.mem_iUnion.mp h
        have ai := (truth t (some i) a ht).mpr (Finset.mem_filter.mp sel).2
        exact unmatched (Set.mem_iUnion.mpr ⟨i,ui,ai⟩)
      let k : K := ⟨t,(truth t none a ht).mp ha,u,ur⟩
      exact Set.mem_iUnion.mpr ⟨e.symm k,by simpa [k] using And.intro ur ht⟩
    · intro h
      obtain ⟨t,ur,ht⟩ := Set.mem_iUnion.mp h
      exact ⟨⟨ur.1,(truth (e t).val none a ht).mpr (e t).property.1⟩,remaining ur ht⟩

end GeneralizedEuler.Section4
