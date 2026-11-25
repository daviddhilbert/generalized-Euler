module

public import Section2.ImmediateBackAndForth
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Back-and-forth with saturation used only at small field domains.
The full RV sort stays named throughout. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder Cardinal

universe u v w z

private theorem exists_monotone_stages {I B : Type*}
    [LinearOrder I] [WellFoundedLT I] [Preorder B] (initial : B) (Valid : I → B → Prop)
    (next : ∀ (i : I) (prev : Set.Iio i → B), Monotone prev →
      (∀ j, Valid j.val (prev j)) → ∃ x, (∀ j, prev j ≤ x) ∧ Valid i x) :
    ∃ f : I → B, Monotone f ∧ ∀ i, Valid i (f i) := by
  classical
  let build (i : I) (earlier : ∀ j : I, j < i → B) : B :=
    let prev : Set.Iio i → B := fun j => earlier j.val j.property
    if h : Monotone prev ∧ ∀ j, Valid j.val (prev j) then
      (next i prev h.1 h.2).choose
    else initial
  let f : I → B := wellFounded_lt.fix build
  have hfix (i : I) : f i = build i (fun j _ => f j) :=
    WellFounded.fix_eq wellFounded_lt build i
  have valid (i : I) : Valid i (f i) ∧ ∀ j < i, f j ≤ f i := by
    apply wellFounded_lt.induction i
    intro i ih
    let prev : Set.Iio i → B := fun j => f j.val
    have hmono : Monotone prev := by
      intro j k hjk
      rcases (show j.val ≤ k.val from hjk).eq_or_lt with he | hl
      · exact le_of_eq (congrArg f he)
      · exact (ih k.val (Set.mem_Iio.mp k.property)).2 j.val hl
    have hvalid (j : Set.Iio i) : Valid j.val (prev j) :=
      (ih j.val (Set.mem_Iio.mp j.property)).1
    have hi : f i = (next i prev hmono hvalid).choose := by
      rw [hfix]
      exact dite_eq_left (And.intro hmono hvalid)
    have hSpec := (next i prev hmono hvalid).choose_spec
    rw [hi]
    exact ⟨hSpec.2, fun j hj => hSpec.1 ⟨j, hj⟩⟩
  refine ⟨f, ?_, fun i => (valid i).1⟩
  intro i j h
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (valid j).2 i h

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {M : SortedStructure L E X}

/-- A stage indexed by a well order uses at most the maximum of
the starting bound and the cardinality of the preceding stages. The
final union can be full-sized, but no one-point extension is taken there. -/
theorem exists_fullVF_and_surjectiveVF_of_small_steps
    {κ μ : Cardinal.{z}} (hμ : ℵ₀ ≤ μ) (hμκ : μ < κ)
    {I : Type z} [LinearOrder I] [WellFoundedLT I] [Nonempty I]
    (enum : I → X .vf) (henum : Function.Surjective enum) (hI : ∀ i : I, #(Set.Iio i) < κ)
    (A : FixedRVLift M M Set.univ) (hsmall : #(A.source.carrier .vf) ≤ μ)
    (step : ∀ B : FixedRVLift M M Set.univ, A ≤ B → #(B.source.carrier .vf) < κ →
      ∀ x : X .vf, ∃ C : FixedRVLift M M Set.univ, B ≤ C ∧
        #(C.source.carrier .vf) ≤ max μ #(B.source.carrier .vf) ∧
        x ∈ C.source.carrier .vf ∧ ∃ y, C.embedding.toEmbedding .vf y = x) :
    ∃ B : FixedRVLift M M Set.univ, A ≤ B ∧ B.source.carrier .vf = Set.univ ∧
      Function.Surjective (B.embedding.toEmbedding .vf) := by
  classical
  let bound (i : I) := max μ #(Set.Iio i)
  have hBound (i : I) : bound i < κ := max_lt hμκ (hI i)
  have hMono : Monotone bound := fun i j hij =>
    max_le_max le_rfl (Cardinal.mk_le_mk_of_subset (Set.Iio_subset_Iio hij))
  let Valid (i : I) (B : FixedRVLift M M Set.univ) : Prop :=
    A ≤ B ∧ #(B.source.carrier .vf) ≤ bound i ∧ enum i ∈ B.source.carrier .vf ∧
      ∃ y, B.embedding.toEmbedding .vf y = enum i
  have next (i : I) (p : Set.Iio i → FixedRVLift M M Set.univ) (hp : Monotone p)
      (hValid : ∀ j, Valid j.val (p j)) : ∃ B, (∀ j, p j ≤ B) ∧ Valid i B := by
    have hPrev : ∃ B : FixedRVLift M M Set.univ, A ≤ B ∧ #(B.source.carrier .vf) ≤ bound i ∧
        ∀ j, p j ≤ B := by
      by_cases hi : Nonempty (Set.Iio i)
      · let := hi
        let B := FixedRVLift.directedUnion p hp
        let j := Classical.choice hi
        refine ⟨B, (hValid j).1.trans (FixedRVLift.le_directedUnion p hp j), ?_,
          FixedRVLift.le_directedUnion p hp⟩
        rw [FixedRVLift.directedUnion_carrier]
        have hsup : (⨆ j, #((p j).source.carrier .vf)) ≤ bound i :=
          ciSup_le fun j => (hValid j).2.1.trans (hMono (Set.mem_Iio.mp j.property).le)
        calc
          #(⋃ j, (p j).source.carrier .vf : Set (X .vf)) ≤
              Cardinal.sum (fun j => #((p j).source.carrier .vf)) := Cardinal.mk_iUnion_le_sum_mk
          _ ≤ #(Set.Iio i) * (⨆ j, #((p j).source.carrier .vf)) := Cardinal.sum_le_mk_mul_iSup _
          _ ≤ bound i * bound i := mul_le_mul' (le_max_right _ _) hsup
          _ = bound i := Cardinal.mul_eq_self (hμ.trans (le_max_left _ _))
      · exact ⟨A, le_rfl, hsmall.trans (le_max_left _ _), fun j => (hi ⟨j⟩).elim⟩
    obtain ⟨B, hAB, hsB, hpB⟩ := hPrev
    obtain ⟨C, hBC, hsC, hdom, hran⟩ := step B hAB (hsB.trans_lt (hBound i)) (enum i)
    exact ⟨C, fun j => (hpB j).trans hBC, hAB.trans hBC,
      hsC.trans (max_le (le_max_left _ _) hsB), hdom, hran⟩
  obtain ⟨f, hf, hValid⟩ := exists_monotone_stages A Valid next
  let B := FixedRVLift.directedUnion f hf
  have hAB : A ≤ B := by
    let i : I := Classical.choice inferInstance
    exact (hValid i).1.trans (FixedRVLift.le_directedUnion f hf i)
  refine ⟨B, hAB, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, rfl⟩ := henum x
    have hi := (FixedRVLift.le_iff_extends _ _).mp (FixedRVLift.le_directedUnion f hf i)
    exact hi.choose .vf (hValid i).2.2.1
  · intro x
    obtain ⟨i, rfl⟩ := henum x
    obtain ⟨y, hy⟩ := (hValid i).2.2.2
    obtain ⟨hmem, he⟩ := (FixedRVLift.le_iff_extends _ _).mp (FixedRVLift.le_directedUnion f hf i)
    exact ⟨⟨y.val, hmem .vf y.property⟩, (he .vf y).symm.trans hy⟩

theorem mk_reverse_field (A : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hA : Function.Surjective (A.embedding.toEmbedding .rv)) :
    #((A.reverse hA).source.carrier .vf) = #(A.source.carrier .vf) := by
  rw [reverse_carrier]
  exact Cardinal.mk_range_eq _ (A.embedding.toEmbedding .vf).injective

/-- Reversing the partial map preserves the size of its field domain,
so a small forth step also supplies a small back step. -/
theorem exists_back_extension_of_small_forth {κ μ : Cardinal.{z}}
    (A : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hA : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val)
    (hsA : #(A.source.carrier .vf) < κ)
    (hforth : ∀ B : FixedRVLift M M (Set.univ : Set (X .rv)),
      (∀ t : B.source.carrier .rv, B.embedding.toEmbedding .rv t = t.val) →
      #(B.source.carrier .vf) < κ → ∀ x : X .vf,
        ∃ C : FixedRVLift M M (Set.univ : Set (X .rv)),
          B ≤ C ∧ #(C.source.carrier .vf) ≤ max μ #(B.source.carrier .vf) ∧ x ∈ C.source.carrier .vf)
    (y : X .vf) :
    ∃ C : FixedRVLift M M (Set.univ : Set (X .rv)),
      A ≤ C ∧ #(C.source.carrier .vf) ≤ max μ #(A.source.carrier .vf) ∧
        ∃ x, C.embedding.toEmbedding .vf x = y := by
  let B := A.reverse (ontoRV_of_fixesRV A hA)
  have hB := reverse_fixesRV A hA
  have hCardB : #(B.source.carrier .vf) = #(A.source.carrier .vf) :=
    mk_reverse_field A (ontoRV_of_fixesRV A hA)
  obtain ⟨D, hBD, hsD, hy⟩ := hforth B hB (hCardB.symm ▸ hsA) y
  have hD := fixesRV_of_extends hBD hB
  let C := D.reverse (ontoRV_of_fixesRV D hD)
  have hCardC : #(C.source.carrier .vf) = #(D.source.carrier .vf) :=
    mk_reverse_field D (ontoRV_of_fixesRV D hD)
  refine ⟨C, le_reverse_of_reverse_le A D _ _ hBD, ?_, reverse_hits_vf D _ ⟨y, hy⟩⟩
  rwa [hCardC, ← hCardB]

/-- Cardinal-bounded version of the automorphism argument. Over the
field's initial ordinal, all proper stages have smaller field domains. -/
theorem exists_immediate_automorphism_of_small_forth
    [Nonempty (X .vf)] {μ : Cardinal.{z}} (hμ : ℵ₀ ≤ μ) (hμκ : μ < #(X .vf))
    (A : FixedRVLift M M (Set.univ : Set (X .rv)))
    (hA : ∀ t : A.source.carrier .rv, A.embedding.toEmbedding .rv t = t.val)
    (hsA : #(A.source.carrier .vf) ≤ μ)
    (hforth : ∀ B : FixedRVLift M M (Set.univ : Set (X .rv)),
      (∀ t : B.source.carrier .rv, B.embedding.toEmbedding .rv t = t.val) →
      #(B.source.carrier .vf) < #(X .vf) → ∀ x : X .vf,
        ∃ C : FixedRVLift M M (Set.univ : Set (X .rv)),
          B ≤ C ∧ #(C.source.carrier .vf) ≤ max μ #(B.source.carrier .vf) ∧ x ∈ C.source.carrier .vf) :
    ∃ f : SortedIsomorphism M M,
      (∀ s (x : A.source.carrier s), f.toEmbedding s x.val = A.embedding.toEmbedding s x) ∧
      ∀ t : X .rv, f.toEmbedding .rv t = t := by
  classical
  let I := (#(X .vf)).ord.ToType
  have hCard : #I = #(X .vf) := Cardinal.mk_ord_toType _
  let enum : I ≃ X .vf := (Cardinal.eq.mp hCard).some
  let : Nonempty I := (inferInstance : Nonempty (X .vf)).map enum.symm
  have hSmall (i : I) : #(Set.Iio i) < #(X .vf) := by
    apply (Cardinal.mk_Iio_lt i ?_).trans_eq hCard
    rw [hCard]
    exact (Ordinal.type_toType _).symm
  obtain ⟨B, hAB, hdom, hran⟩ :=
    exists_fullVF_and_surjectiveVF_of_small_steps hμ hμκ enum enum.surjective hSmall A hsA (by
      intro B hAB hsB x
      obtain ⟨C, hBC, hsC, hx⟩ := hforth B (fixesRV_of_extends hAB hA) hsB x
      have hcSmall : #(C.source.carrier .vf) < #(X .vf) := hsC.trans_lt (max_lt hμκ hsB)
      obtain ⟨D, hCD, hsD, hr⟩ := exists_back_extension_of_small_forth C
        (fixesRV_of_extends (hAB.trans hBC) hA) hcSmall hforth x
      refine ⟨D, hBC.trans hCD, hsD.trans (max_le (le_max_left _ _) hsC), ?_, hr⟩
      exact ((FixedRVLift.le_iff_extends C D).mp hCD).choose .vf hx)
  exact FixedRVLift.exists_immediate_automorphism_of_fullVF hA B hAB hdom hran

end GeneralizedEuler.Section2
