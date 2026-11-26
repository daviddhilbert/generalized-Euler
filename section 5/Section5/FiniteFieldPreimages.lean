module

public import Section5.CoordinatePreparation

/-! Finiteness of the possible original field tuples over one image
field tuple. This property preserves finite auxiliary fibers. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] {O : ValuationSubring K}
  {F F' F'' I J R : Type*}

/-- The RV input is allowed to vary when taking a field preimage. -/
@[expose] def fieldPreimages
    (f : PreparationPoint O F I → PreparationPoint O F' J) (y : F' → K) : Set (F → K) :=
  {x | ∃ t, (f (x,t)).1 = y}

abbrev FiniteFieldPreimages (f : PreparationPoint O F I → PreparationPoint O F' J) :=
  ∀ y, (fieldPreimages f y).Finite

namespace FiniteFieldPreimages

theorem id : FiniteFieldPreimages (O := O) (_root_.id : PreparationPoint O F I → _) := by
  intro y
  exact (Set.finite_singleton y).subset (fun _ h => h.choose_spec)

theorem comp
    {f : PreparationPoint O F I → PreparationPoint O F' J}
    {g : PreparationPoint O F' J → PreparationPoint O F'' R}
    (hf : FiniteFieldPreimages f) (hg : FiniteFieldPreimages g) :
    FiniteFieldPreimages (g ∘ f) := by
  intro y
  apply ((hg y).biUnion (fun z _ => hf z)).subset
  rintro x ⟨t,ht⟩
  let q := f (x,t)
  exact Set.mem_iUnion₂.mpr ⟨q.1,⟨q.2,ht⟩,t,rfl⟩

theorem image_finite_fibers
    {f : PreparationPoint O F I → PreparationPoint O F' J}
    (hf : FiniteFieldPreimages f) (A : Set (PreparationPoint O F I))
    (hA : ∀ x, {ξ | (x,ξ) ∈ A}.Finite) (y : F' → K) :
    {s | (y,s) ∈ f '' A}.Finite := by
  let candidates (x : F → K) : Set (J → RV0 O) :=
    (fun t => (f (x,t)).2) '' {t | (x,t) ∈ A}
  have hfin (x) : (candidates x).Finite := (hA x).image _
  apply ((hf y).biUnion (fun x _ => hfin x)).subset
  rintro s ⟨⟨x,t⟩, hx, he⟩
  exact Set.mem_iUnion₂.mpr ⟨x,⟨t,congrArg Prod.fst he⟩,t,hx,congrArg Prod.snd he⟩

end FiniteFieldPreimages

end GeneralizedEuler.Section5
