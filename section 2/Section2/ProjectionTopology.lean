module

public import Section2.Dimension
public import Mathlib.Topology.Bases
public import Mathlib.SetTheory.Cardinal.Finite

/-! Comparing projection dimensions through coordinatewise open
embeddings. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open Topology

/-- Projection dimension for an arbitrary finite coordinate type. -/
@[expose]
def finiteTupleProjectionDimension {X : Type*} [TopologicalSpace X] {I : Type} [Finite I]
    (D : Set (I → X)) : ℕ := by
  classical
  exact ((Finset.range (Nat.card I + 1)).filter
    (fun k => ∃ e : Fin k ↪ I, (interior ((fun x : I → X => x ∘ e) '' D)).Nonempty)).sup id

theorem finiteTupleProjectionDimension_fin {X : Type*} [TopologicalSpace X] {n : ℕ}
    (D : Set (Fin n → X)) : finiteTupleProjectionDimension D = projectionDimension D := by
  classical
  rw [finiteTupleProjectionDimension, projectionDimension, Nat.card_fin]
  rfl

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem nonempty_interior_image_iff {f : X → Y} (hf : IsOpenEmbedding f) (U : Set X) :
    (interior (f '' U)).Nonempty ↔ (interior U).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, _, rfl⟩ := interior_subset hy
    have h : f ⁻¹' interior (f '' U) ⊆ U := by
      intro z hz
      obtain ⟨w, hw, he⟩ := interior_subset hz
      exact hf.injective he ▸ hw
    exact ⟨x, interior_maximal h (isOpen_interior.preimage hf.continuous) hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨f x, interior_maximal (Set.image_mono interior_subset)
      (hf.isOpenMap _ isOpen_interior) ⟨x, hx, rfl⟩⟩

private theorem nonempty_interior_of_coordinatewise_open {I : Type} [Finite I]
    (f : X → Y) (region : I → Set X) (U : Set (I → X))
    (hU : ∀ x ∈ U, ∀ i, x i ∈ region i)
    (hOpen : ∀ i, IsOpen (region i))
    (hf : ∀ i, IsOpenEmbedding (fun x : region i => f x.val)) :
    (interior ((fun x : I → X => f ∘ x) '' U)).Nonempty ↔ (interior U).Nonempty := by
  let base : (∀ i, region i) → (I → X) := fun x i => (x i).val
  let mapped : (∀ i, region i) → (I → Y) := fun x i => f (x i).val
  let D := base ⁻¹' U
  have hBase : IsOpenEmbedding base := .piMap (fun i => (hOpen i).isOpenEmbedding_subtypeVal)
  have hmapped : IsOpenEmbedding mapped := .piMap hf
  have hb : base '' D = U := by
    ext x
    exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hx => ⟨fun i => ⟨x i, hU x hx i⟩, hx, rfl⟩⟩
  have hm : mapped '' D = (fun x : I → X => f ∘ x) '' U := by
    rw [← hb, Set.image_image]
    rfl
  rw [← hm, ← hb, nonempty_interior_image_iff hmapped, nonempty_interior_image_iff hBase]

private theorem nonempty_interior_image_of_dense_regions {I T : Type} [Finite I]
    (f : X → Y) (hf : Function.Injective f) (region : T → Set X) (D : Set (I → X))
    (hOpen : ∀ t, IsOpen (region t))
    (hEmbed : ∀ t, IsOpenEmbedding (fun x : region t => f x.val))
    (hDense : Dense (⋃ t, region t))
    {V : Set Y} (hV : Dense V)
    (hCover : ∀ x, f x ∈ V → ∃ t, x ∈ region t) :
    (interior ((fun x : I → X => f ∘ x) '' D)).Nonempty ↔ (interior D).Nonempty := by
  let F : (I → X) → (I → Y) := fun x => f ∘ x
  have chart (tag : I → T) :
      let U := Set.pi Set.univ (region ∘ tag)
      let W := Set.pi Set.univ (fun i => f '' region (tag i))
      IsOpen U ∧ IsOpen W ∧ F '' (D ∩ U) = (F '' D) ∩ W := by
    intro U W
    refine ⟨isOpen_set_pi Set.finite_univ (fun i _ => hOpen (tag i)),
      isOpen_set_pi Set.finite_univ (fun i _ => ?_), ?_⟩
    · convert (hEmbed (tag i)).isOpen_range using 1
      ext y
      exact ⟨fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩, fun ⟨x, hy⟩ => ⟨x.val, x.property, hy⟩⟩
    · ext y
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx.1, rfl⟩, fun i hi => ⟨x i, hx.2 i hi, rfl⟩⟩
      · rintro ⟨⟨x, hx, rfl⟩, hy⟩
        refine ⟨x, ⟨hx, fun i hi => ?_⟩, rfl⟩
        obtain ⟨z, hz, he⟩ := hy i hi
        exact hf he ▸ hz
  have transport (tag : I → T) :
      let U := Set.pi Set.univ (region ∘ tag)
      (interior (F '' (D ∩ U))).Nonempty ↔ (interior (D ∩ U)).Nonempty :=
    nonempty_interior_of_coordinatewise_open f (region ∘ tag) _
      (fun _ hx i => hx.2 i (Set.mem_univ i)) (fun i => hOpen (tag i)) (fun i => hEmbed (tag i))
  constructor
  · intro h
    have hd : Dense (Set.pi Set.univ (fun _ : I => V)) :=
      dense_pi Set.univ (fun _ _ => hV)
    obtain ⟨y, hy, hyV⟩ := hd.inter_open_nonempty _ isOpen_interior h
    obtain ⟨x, _, rfl⟩ := interior_subset hy
    choose tag ht using fun i => hCover (x i) (hyV i (Set.mem_univ i))
    obtain ⟨_, hw, he⟩ := chart tag
    have hx : F x ∈ interior (F '' (D ∩ Set.pi Set.univ (region ∘ tag))) := by
      rw [he]
      exact interior_maximal (Set.inter_subset_inter_left _ interior_subset)
        (isOpen_interior.inter hw) ⟨hy, fun i _ => ⟨x i, ht i, rfl⟩⟩
    exact ((transport tag).mp ⟨F x, hx⟩).mono (interior_mono Set.inter_subset_left)
  · intro h
    have hd : Dense (Set.pi Set.univ (fun _ : I => ⋃ t, region t)) :=
      dense_pi Set.univ (fun _ _ => hDense)
    obtain ⟨x, hx, hxU⟩ := hd.inter_open_nonempty _ isOpen_interior h
    choose tag ht using fun i => Set.mem_iUnion.mp (hxU i (Set.mem_univ i))
    obtain ⟨hu, _, _⟩ := chart tag
    have hx' : x ∈ interior (D ∩ Set.pi Set.univ (region ∘ tag)) :=
      interior_maximal (Set.inter_subset_inter_left _ interior_subset)
        (isOpen_interior.inter hu) ⟨hx, fun i _ => ht i⟩
    exact ((transport tag).mpr ⟨x, hx'⟩).mono
      (interior_mono (Set.image_mono Set.inter_subset_left))

/-- Coordinatewise images preserve projection dimension if open
regions cover a dense subset of the source and all preimages of a
dense subset of the target. -/
theorem finiteTupleProjectionDimension_image_of_dense_regions {I T : Type} [Finite I]
    (f : X → Y) (hf : Function.Injective f) (region : T → Set X) (D : Set (I → X))
    (hOpen : ∀ t, IsOpen (region t))
    (hEmbed : ∀ t, IsOpenEmbedding (fun x : region t => f x.val))
    (hDense : Dense (⋃ t, region t))
    {V : Set Y} (hV : Dense V)
    (hCover : ∀ x, f x ∈ V → ∃ t, x ∈ region t) :
    finiteTupleProjectionDimension ((fun x : I → X => f ∘ x) '' D) =
      finiteTupleProjectionDimension D := by
  classical
  have h (k : ℕ) (e : Fin k ↪ I) :
      (interior ((fun x : I → Y => x ∘ e) '' ((fun x : I → X => f ∘ x) '' D))).Nonempty ↔
        (interior ((fun x : I → X => x ∘ e) '' D)).Nonempty := by
    have heq : (fun x : I → Y => x ∘ e) '' ((fun x : I → X => f ∘ x) '' D) =
        (fun x : Fin k → X => f ∘ x) '' ((fun x : I → X => x ∘ e) '' D) := by
      rw [Set.image_image, Set.image_image]
      rfl
    rw [heq]
    exact nonempty_interior_image_of_dense_regions f hf region _ hOpen hEmbed hDense hV hCover
  unfold finiteTupleProjectionDimension
  congr 1
  ext k
  simp only [Finset.mem_filter, h]

end GeneralizedEuler.Section2
