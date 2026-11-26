module

public import Section5.FiniteCenters

/-! Finite RV fibers after unary preparation and the zero pattern in the
unary case of Corollary 5.8. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] {O : ValuationSubring K}

namespace UnaryPreparation

variable {H I : Type*} (P : UnaryPreparation O H)

theorem finite_prepared_offsets {C : Type*} (center : C → K) (cs : List C) :
    (Set.range ((regularize (O := O)).prepare center cs).offset).Finite := by
  classical
  let centers : Finset K := insert 0 (cs.toFinset.image center)
  apply centers.finite_toSet.subset
  rintro d ⟨t, rfl⟩
  exact (regularize (O := O)).prepare_offset_mem center (centers : Set K)
    (fun _ => Finset.mem_insert_self _ _) cs
    (fun c hc => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hc))) t

/-- Each new field fiber comes from finitely many original field fibers.
This uses the finite set of translation offsets and applies for every
RV tuple arity. -/
theorem finite_fibers_image (A : Set (K × I)) (hA : ∀ x, {ξ | (x, ξ) ∈ A}.Finite)
    (hoff : (Set.range P.offset).Finite) (y : K) :
    {t : H × I | ((y, t.1), t.2) ∈ (fun p : K × I => (P.map p.1, p.2)) '' A}.Finite := by
  let B (d : K) : Set (H × I) :=
    (fun ξ => (P.label (y + d), ξ)) '' {ξ | (y + d, ξ) ∈ A}
  apply (hoff.biUnion (fun d _ => (hA (y + d)).image (fun ξ => (P.label (y + d), ξ)))).subset
  rintro ⟨t, ξ⟩ ⟨⟨x, ζ⟩, hx, he⟩
  have hmap : P.map x = (y, t) := congrArg Prod.fst he
  have hξ : ζ = ξ := congrArg Prod.snd he
  rw [hξ] at hx
  have ht : P.label x = t := congrArg Prod.snd hmap
  have hcoord : x - P.offset (P.label x) = y := congrArg Prod.fst hmap
  have hxd : x = y + P.offset (P.label x) := eq_add_of_sub_eq hcoord
  apply Set.mem_iUnion₂.mpr
  refine ⟨P.offset (P.label x), Set.mem_range_self _, ?_⟩
  change (t, ξ) ∈ B (P.offset (P.label x))
  exact ⟨ξ, hxd ▸ hx, Prod.ext ((congrArg P.label hxd).symm.trans ht) rfl⟩

/-- The structure map on the RV labels is finite-to-one. In particular
the labels with leading term zero form a finite set, and can be assigned
degree zero. The other labels retain their nonzero lead in degree one. -/
theorem finite_rv_labels (A : Set (K × I)) (hA : ∀ x, {ξ | (x, ξ) ∈ A}.Finite)
    (hoff : (Set.range P.offset).Finite)
    (hmember : ∀ x y ξ, P.label x = P.label y → ((x, ξ) ∈ A ↔ (y, ξ) ∈ A))
    (s : RV0 O) :
    {t : H × I | P.lead t.1 = s ∧ ∃ x, (x, t.2) ∈ A ∧ P.label x = t.1}.Finite := by
  obtain ⟨y, hy⟩ := rv_surjective O s
  apply (P.finite_fibers_image A hA hoff y).subset
  rintro ⟨t, ξ⟩ ⟨ht, x, hx, hxt⟩
  change ((y, t), ξ) ∈ (fun p : K × I => (P.map p.1, p.2)) '' A
  rw [P.image_restriction A hmember]
  exact ⟨hy.trans ht.symm, x, hx, hxt⟩

end UnaryPreparation

end GeneralizedEuler.Section5
