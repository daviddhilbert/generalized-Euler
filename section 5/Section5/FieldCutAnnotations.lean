module

public import Section5.CutFieldFamilies

/-! The annotation of a finite partition identifies every original
piece with a restriction on the new RV tags and fixes the fields. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}
  {n k q : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem field_cut_annotation
    (A : RetainedFieldFamily 𝓜 S n k)
    (D : Fin q → MixedCarrier Z n A.tags) (d : ∀ i, SortedDefinableOver 𝓜 S.carrier (D i))
    (sub : ∀ i, D i ⊆ {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier})
    (disj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (cover : ∀ a : SortedAssignment Z (MixedVariables n A.tags), mixedTuple a ∈ A.carrier → ∃ i, a ∈ D i) :
    ∃ (B : RetainedFieldFamily 𝓜 S n k) (pieces : Fin q → Set (B.tags → RV0 O))
      (defPieces : ∀ i, isRVSet 𝓜 S (pieces i)),
      Pairwise (fun i j => Disjoint (pieces i) (pieces j)) ∧
      (∀ b t, (b,t) ∈ B.carrier → ∃ i, t ∈ pieces i) ∧
      (∃ f : MixedGraphIso 𝓜 S
        {a : SortedAssignment Z (MixedVariables n A.tags) | mixedTuple a ∈ A.carrier}
        {b : SortedAssignment Z (MixedVariables n B.tags) | mixedTuple b ∈ B.carrier},
        (∀ a, (f.equiv a).val .vf = a.val .vf) ∧
        (∀ a, (f.equiv a).val .rv ∘ B.select = a.val .rv ∘ A.select)) ∧
      ∀ i, let A' := A.cutCarrier (D i) (d i) (sub i)
        let B' := B.restrictTags (pieces i) (defPieces i)
        ∃ f : MixedGraphIso 𝓜 S
          {a : SortedAssignment Z (MixedVariables n A'.tags) | mixedTuple a ∈ A'.carrier}
          {b : SortedAssignment Z (MixedVariables n B'.tags) | mixedTuple b ∈ B'.carrier},
          (∀ a, (f.equiv a).val .vf = a.val .vf) ∧
          (∀ a, (f.equiv a).val .rv ∘ B'.select = a.val .rv ∘ A'.select) := by
  let code := fieldPartitionCode D
  let dc := fieldPartitionCode_graph D d
  let B := A.withRecordedLabels code dc
  let tags (i : Fin q) : Set (B.tags → RV0 O) := fieldPartitionTag i
  let dt (i : Fin q) : isRVSet 𝓜 S (tags i) := fieldPartitionTag_definable i
  obtain ⟨e,fix,keep⟩ := A.withRecordedLabels_iso code dc
  refine ⟨B,tags,dt,fieldPartitionTag_disjoint,?_,⟨e,fix,fun a => congrArg (· ∘ A.select) (keep a)⟩,?_⟩
  · intro x t ht
    obtain ⟨a,_,ha,eval⟩ := (show (x,t) ∈ A.recordedCarrier code from ht)
    obtain ⟨i,hi⟩ := cover a ha
    exact ⟨i,(fieldPartitionTag_code_iff D disj a t eval.symm i).2 hi⟩
  · intro i A' B'
    let X := MixedVariables n A.tags
    let Y := MixedVariables n B.tags
    let L := {a : SortedAssignment Z X | mixedTuple a ∈ A.carrier}
    let R := {b : SortedAssignment Z Y | mixedTuple b ∈ B.carrier}
    let Cut := {b : SortedAssignment Z Y | mixedTuple b ∈ B'.carrier}
    have marked (a : L) : (e.equiv a).val .rv ∈ tags i ↔ a.val ∈ D i := by
      let b := (e.equiv a).val
      have ret : A.recordedForget b = a.val := mixedTuple_injective (Prod.ext (fix a) (keep a))
      have fresh := ((A.recordedCarrier_mem code b).1 (e.equiv a).property).2
      rw [ret] at fresh
      exact fieldPartitionTag_code_iff D disj a.val (b .rv) fresh.symm i
    have eq : e.rangeOver (sub i) = Cut := by
      ext b
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨(e.equiv _).property,(marked _).2 a.property⟩
      · intro h
        have hb : b ∈ R := h.1
        let a := e.equiv.symm ⟨b,hb⟩
        have same : e.equiv a = ⟨b,hb⟩ := e.equiv.apply_symm_apply _
        have mark : (e.equiv a).val .rv ∈ tags i := by rw [same]; exact h.2
        exact ⟨⟨a.val,(marked a).1 mark⟩,congrArg Subtype.val same⟩
    let g : MixedGraphIso 𝓜 S (D i) Cut := eq ▸ e.restrict (sub i) (d i)
    have eval (a : D i) : (g.equiv a).val = (e.equiv ⟨a.val,sub i a.property⟩).val := by
      have tr (Y' : Set (SortedAssignment Z Y)) (h : e.rangeOver (sub i) = Y') :
          ((h ▸ e.restrict (sub i) (d i) : MixedGraphIso 𝓜 S (D i) Y').equiv a).val =
            (e.equiv ⟨a.val,sub i a.property⟩).val := by
        cases h
        exact e.restrict_apply (sub i) (d i) a
      exact tr _ eq
    let Source := {a : SortedAssignment Z X | mixedTuple a ∈ A'.carrier}
    have source : Source = D i := A.cutCarrier_as_set (D i) (d i) (sub i)
    have compare (D' : Set (SortedAssignment Z X)) (h : D i = D') :
        ∃ f : MixedGraphIso 𝓜 S D' Cut, (∀ a, (f.equiv a).val .vf = a.val .vf) ∧
          (∀ a, (f.equiv a).val .rv ∘ B'.select = a.val .rv ∘ A'.select) := by
      cases h
      refine ⟨g,?_,?_⟩
      · intro a
        exact (congrFun (eval a) .vf).trans (fix ⟨a.val,sub i a.property⟩)
      · intro a
        exact (congrArg (fun a => a .rv ∘ B'.select) (eval a)).trans
          (congrArg (· ∘ A.select) (keep ⟨a.val,sub i a.property⟩))
    exact compare Source source.symm

end GeneralizedEuler.Section5
