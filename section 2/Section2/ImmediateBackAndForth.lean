module

public import Section2.ImmediateIdentity

/-! Reversing the fixed-RV maps in the back-and-forth of Lemma 2.20. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z z'

variable {L : Language.{u, v}} {E : Type w}
  {X : TCsort → Type z} {Y : TCsort → Type z'}
  {M : SortedStructure L E X} {N : SortedStructure L E Y}
  {S : SortedSubstructure M}

/-- The image of a partial sorted embedding is a substructure. -/
@[expose]
def SortedEmbedding.rangeSubstructure (e : SortedEmbedding S.structureOn N) : SortedSubstructure N where
  carrier s := Set.range (e.toEmbedding s)
  closed := by
    intro ss s f a ha
    choose b hb using ha
    exact ⟨S.structureOn.funMap f b, (e.map_fun f b).trans (congrArg (N.funMap f) (funext hb))⟩

private def rangePreimage (e : SortedEmbedding S.structureOn N)
    (s : TCsort) (x : e.rangeSubstructure.carrier s) : S.carrier s := x.property.choose

private theorem rangePreimage_map (e : SortedEmbedding S.structureOn N)
    (s : TCsort) (x : e.rangeSubstructure.carrier s) :
    e.toEmbedding s (rangePreimage e s x) = x.val := x.property.choose_spec

/-- The inverse of a partial sorted embedding on its image. -/
def SortedEmbedding.inverseFromRange (e : SortedEmbedding S.structureOn N) :
    SortedEmbedding e.rangeSubstructure.structureOn M where
  toEmbedding s :=
    ⟨fun x => (rangePreimage e s x).val, fun x y h => Subtype.ext (by
      rw [← rangePreimage_map e s x, ← rangePreimage_map e s y, Subtype.ext h])⟩
  map_fun := by
    intro ss s f a
    let old : SortedArgs (fun s => S.carrier s) ss := fun i => rangePreimage e _ (a i)
    have h : rangePreimage e s (e.rangeSubstructure.structureOn.funMap f a) =
        S.structureOn.funMap f old := by
      apply (e.toEmbedding s).injective
      rw [rangePreimage_map, e.map_fun]
      exact congrArg (N.funMap f) (funext fun i => (rangePreimage_map e _ (a i)).symm)
    exact congrArg Subtype.val h
  map_rel := by
    intro ss r a
    let old : SortedArgs (fun s => S.carrier s) ss := fun i => rangePreimage e _ (a i)
    have h := (e.map_rel r old).symm
    change M.relMap r (fun i => (old i).val) ↔ N.relMap r (fun i => (a i).val)
    rwa [show (fun i => e.toEmbedding _ (old i)) = fun i => (a i).val from
      funext fun i => rangePreimage_map e _ (a i)] at h

@[simp]
theorem SortedEmbedding.inverseFromRange_apply_image (e : SortedEmbedding S.structureOn N)
    (s : TCsort) (x : S.carrier s) (h : e.toEmbedding s x ∈ e.rangeSubstructure.carrier s) :
    e.inverseFromRange.toEmbedding s ⟨e.toEmbedding s x, h⟩ = x.val := by
  change (rangePreimage e s ⟨e.toEmbedding s x, h⟩).val = x.val
  exact congrArg Subtype.val ((e.toEmbedding s).injective (rangePreimage_map e s _))

namespace FixedRVLift

variable {Y : TCsort → Type z} {N : SortedStructure L E Y}

/-- A lift with all its RV values in the image can also be read backwards. -/
@[expose]
def reverse (A : FixedRVLift M N Set.univ)
    (honto : Function.Surjective (A.embedding.toEmbedding .rv)) :
    FixedRVLift N M Set.univ :=
  ⟨A.embedding.rangeSubstructure, Set.range_eq_univ.mpr honto, A.embedding.inverseFromRange⟩

end FixedRVLift

variable {A B : FixedRVLift M M (Set.univ : Set (X .rv))}

theorem fixesRV_of_extends (hAB : A ≤ B)
    (hA : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val) :
    ∀ t : B.source.carrier .rv, B.embedding.toEmbedding .rv t = t.val := by
  obtain ⟨hc, he⟩ := (FixedRVLift.le_iff_extends A B).mp hAB
  intro t
  have ht : t.val ∈ A.source.carrier .rv := A.rv_eq.symm ▸ Set.mem_univ _
  let u : A.source.carrier .rv := ⟨t.val, ht⟩
  exact (he .rv u).symm.trans (hA u)

theorem ontoRV_of_fixesRV (A : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hA : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val) :
    Function.Surjective (A.embedding.toEmbedding .rv) := by
  intro x
  let t : A.source.carrier .rv := ⟨x, A.rv_eq.symm ▸ Set.mem_univ x⟩
  exact ⟨t, hA t⟩

theorem reverse_fixesRV (A : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hA : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val)
    (t : (A.reverse (ontoRV_of_fixesRV A hA)).source.carrier .rv) :
    (A.reverse (ontoRV_of_fixesRV A hA)).embedding.toEmbedding .rv t = t.val := by
  let p := rangePreimage A.embedding .rv t
  exact (hA p).symm.trans (rangePreimage_map A.embedding .rv t)

theorem reverse_carrier (A : FixedRVLift M M (Set.univ : Set (X .rv)))
    (h : Function.Surjective (A.embedding.toEmbedding .rv)) (s : TCsort) :
    (A.reverse h).source.carrier s = Set.range (A.embedding.toEmbedding s) := by rfl

theorem le_reverse_of_reverse_le
    (A D : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hA : Function.Surjective (A.embedding.toEmbedding .rv))
    (hD : Function.Surjective (D.embedding.toEmbedding .rv))
    (hBD : A.reverse hA ≤ D) : A ≤ D.reverse hD := by
  let B := A.reverse hA
  let C := D.reverse hD
  obtain ⟨hBDmem, hBDeq⟩ := (FixedRVLift.le_iff_extends B D).mp hBD
  have hpoint (s : TCsort) (x : A.source.carrier s) :
      ∃ u : D.source.carrier s, u.val = A.embedding.toEmbedding s x ∧ D.embedding.toEmbedding s u = x.val := by
    let t : B.source.carrier s := ⟨A.embedding.toEmbedding s x, Set.mem_range_self x⟩
    let u : D.source.carrier s := ⟨t.val, hBDmem s t.property⟩
    exact ⟨u, rfl, (hBDeq s t).symm.trans (A.embedding.inverseFromRange_apply_image s x t.property)⟩
  have hACmem (s : TCsort) : A.source.carrier s ⊆ C.source.carrier s := by
    intro x hx
    obtain ⟨u, _, he⟩ := hpoint s ⟨x, hx⟩
    exact ⟨u, he⟩
  apply FixedRVLift.le_of_compatible hACmem
  intro s x
  obtain ⟨u, hu, he⟩ := hpoint s x
  have he' : (⟨x.val, hACmem s x.property⟩ : C.source.carrier s) =
        ⟨D.embedding.toEmbedding s u, Set.mem_range_self u⟩ := Subtype.ext he.symm
  rw [he']
  exact hu.symm.trans (D.embedding.inverseFromRange_apply_image s u _).symm

theorem reverse_hits_vf (D : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hD : Function.Surjective (D.embedding.toEmbedding .rv)) (y : D.source.carrier .vf) :
    ∃ x, (D.reverse hD).embedding.toEmbedding .vf x = y.val :=
  ⟨⟨D.embedding.toEmbedding .vf y, Set.mem_range_self y⟩,
    D.embedding.inverseFromRange_apply_image .vf y _⟩

/-- The field-point extension property for maps fixing all of RV
automatically gives the back property, by applying it to the inverse. -/
theorem exists_back_extension_of_immediate_forth
    (A : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hA : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val)
    (hforth : ∀ B : FixedRVLift M M (Set.univ : Set (X .rv)),
      (∀ t : B.source.carrier .rv, B.embedding.toEmbedding .rv t = t.val) → ∀ x : X .vf,
        ∃ C : FixedRVLift M M (Set.univ : Set (X .rv)), B ≤ C ∧ x ∈ C.source.carrier .vf)
    (y : X .vf) :
    ∃ C : FixedRVLift M M (Set.univ : Set (X .rv)), A ≤ C ∧ ∃ x, C.embedding.toEmbedding .vf x = y := by
  let B := A.reverse (ontoRV_of_fixesRV A hA)
  have hB : ∀ t : B.source.carrier .rv, B.embedding.toEmbedding .rv t = t.val := reverse_fixesRV A hA
  obtain ⟨D, hBD, hy⟩ := hforth B hB y
  have hD := fixesRV_of_extends hBD hB
  let C := D.reverse (ontoRV_of_fixesRV D hD)
  exact ⟨C, le_reverse_of_reverse_le A D _ _ hBD, reverse_hits_vf D _ ⟨y, hy⟩⟩

/-- Lemma 2.20 after supplying the one-field-point extension step.
The two directions and the initial extension by identity follow formally. -/
theorem exists_immediate_automorphism_of_field_step (S : SortedSubstructure M)
    (e : SortedEmbedding S.structureOn M)
    (he : ∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val)
    (hforth : ∀ B : FixedRVLift M M (Set.univ : Set (X .rv)),
      (∀ t : B.source.carrier .rv, B.embedding.toEmbedding .rv t = t.val) → ∀ x : X .vf,
        ∃ C : FixedRVLift M M (Set.univ : Set (X .rv)), B ≤ C ∧ x ∈ C.source.carrier .vf) :
    ∃ f : SortedIsomorphism M M,
      (∀ s (x : S.carrier s), f.toEmbedding s x.val = e.toEmbedding s x) ∧
      ∀ t : X .rv, f.toEmbedding .rv t = t := by
  let A := e.extendImmediateByIdentity S he
  have hA := e.extendImmediateByIdentity_fixesRV S he
  obtain ⟨f, hmap, hfix⟩ := FixedRVLift.exists_immediate_automorphism (A := A) hA
    (fun B hAB => hforth B (fixesRV_of_extends hAB hA))
    (fun B hAB => exists_back_extension_of_immediate_forth B (fixesRV_of_extends hAB hA) hforth)
  refine ⟨f, fun s x => ?_, hfix⟩
  have hx : x.val ∈ A.source.carrier s := by
    cases s with
    | vf => exact (e.extendImmediateByIdentity_carrier_vf S he).symm ▸ x.property
    | rv => exact A.rv_eq.symm ▸ Set.mem_univ _
  exact (hmap s ⟨x.val, hx⟩).trans (e.extendImmediateByIdentity_agrees S he s x hx)

end GeneralizedEuler.Section2
