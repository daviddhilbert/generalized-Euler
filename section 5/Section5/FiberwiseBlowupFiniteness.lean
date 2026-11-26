module

public import Mathlib.Data.Set.Finite.Lattice

/-! Check the finite deletion condition after gluing the fiberwise
blowup schemes of Lemma 5.36. -/

public section

namespace GeneralizedEuler.Section5

variable {I H T : Type*} {A : I → Type*}

/-- The selected coordinates determine finitely many indices. After
fixing any one of those indices, the remaining deletion condition is
the local one on that slice. -/
theorem finite_deleted_label_fibers_of_retained_indices
    (head : I → H) (tail : ∀ i, A i → T)
    (finiteHead : ∀ h, (head ⁻¹' {h}).Finite)
    (finiteTail : ∀ i t, (tail i ⁻¹' {t}).Finite) :
    ∀ y : H × T, ((fun a : Σ i, A i => (head a.1,tail a.1 a.2)) ⁻¹' {y}).Finite := by
  intro y
  let slice (i : I) : Set (Σ i, A i) := Sigma.mk i '' (tail i ⁻¹' {y.2})
  have hSlice (i : I) : (slice i).Finite := (finiteTail i y.2).image _
  apply ((finiteHead y.1).biUnion (fun i _ => hSlice i)).subset
  rintro ⟨i,a⟩ ha
  have he : (head i,tail i a) = y := ha
  exact Set.mem_iUnion₂.2 ⟨i,congrArg Prod.fst he,a,congrArg Prod.snd he,rfl⟩

end GeneralizedEuler.Section5
