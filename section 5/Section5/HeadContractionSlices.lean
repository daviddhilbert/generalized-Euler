module

public import Section5.HeadContractionLift
public import Section5.RetainedCoordinateSlices
public import Section5.MixedGraphIsomorphisms

/-! Comparing two head contractions can be done over each fixed
old RV tuple. Both preparations lift to fixed-base isomorphisms
on that slice, and the slice retains every RV tag. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n k : ℕ} {A : RetainedFieldFamily M S (n+1) k}

namespace HeadContractionData

variable (H : HeadContractionData A)

@[expose] def liftedSlice (v : Fin k → RV0 O) :
    Set (PreparationPoint O (Fin (n+1)) H.target.tags) :=
  {q ∈ H.liftedCarrier | q.2 ∘ H.target.select ∘ Fin.castSucc = v}

theorem liftPoint_slice_image (v : Fin k → RV0 O) :
    H.liftPoint '' A.selectedFiber v = H.liftedSlice v := by
  ext q
  constructor
  · rintro ⟨p,⟨hp,ht⟩,rfl⟩
    refine ⟨?_,(H.liftPoint_preserves_selected p).trans ht⟩
    rw [← H.liftPoint_image]
    exact ⟨p,hp,rfl⟩
  · rintro ⟨hq,ht⟩
    rw [← H.liftPoint_image] at hq
    obtain ⟨p,hp,rfl⟩ := hq
    exact ⟨p,⟨hp,(H.liftPoint_preserves_selected p).symm.trans ht⟩,rfl⟩

theorem liftedSlice_equivalence (p : SortedAssignment (CanonicalSort O) (RVVariables (Fin k))) :
    Nonempty (MixedGraphIso M (M.termGenerated (namedTuple S p))
      {a : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.selectedFiber (p .rv)}
      {b : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) H.target.tags) | mixedTuple b ∈ H.liftedSlice (p .rv)}) := by
  let T := M.termGenerated (namedTuple S p)
  let U := MixedVariables (n+1) A.tags
  let V := MixedVariables (n+1) H.target.tags
  let source : Set (SortedAssignment (CanonicalSort O) U) := {a | mixedTuple a ∈ A.selectedFiber (p .rv)}
  let target : Set (SortedAssignment (CanonicalSort O) V) := {b | mixedTuple b ∈ H.liftedSlice (p .rv)}
  let pack : SortedAssignment (CanonicalSort O) V ≃ PreparationPoint O (Fin (n+1)) H.target.tags :=
    Equiv.ofBijective mixedTuple ⟨mixedTuple_injective,mixedTuple_surjective⟩
  let f (a : source) := pack.symm (H.liftPoint (mixedTuple a.val))
  have evaluate (a : source) : mixedTuple (f a) = H.liftPoint (mixedTuple a.val) := pack.apply_symm_apply _
  have inj : Function.Injective f := by
    intro a b eq
    exact Subtype.ext (mixedTuple_injective (H.liftPoint_injective (by rw [← evaluate,← evaluate,eq])))
  have sub : ∀ s, S.carrier s ⊆ T.carrier s := fun s x hx =>
    (M.termGeneratedAssignment (namedTuple S p) s (.inl ⟨x,hx⟩)).property
  have graph : DefinableRelation M T.carrier (fun (a : SortedAssignment (CanonicalSort O) U)
      (b : SortedAssignment (CanonicalSort O) V) => H.liftPoint (mixedTuple a) = mixedTuple b) := by
    unfold DefinableRelation
    exact H.liftPoint_definable.mono sub
  have sourceDef : SortedDefinableOver M T.carrier source := A.selectedFiber_definable p
  have fDef : DefinableRelation M T.carrier (fun a b => ∃ h : a ∈ source, f ⟨a,h⟩ = b) := by
    apply (graph.inter_left sourceDef).congr
    intro a b
    constructor
    · rintro ⟨eq,ha⟩
      exact ⟨ha,mixedTuple_injective ((evaluate ⟨a,ha⟩).trans eq)⟩
    · rintro ⟨ha,rfl⟩
      exact ⟨(evaluate ⟨a,ha⟩).symm,ha⟩
  have range : Set.range f = target := by
    ext b
    constructor
    · rintro ⟨x,rfl⟩
      change mixedTuple (f x) ∈ H.liftedSlice (p .rv)
      rw [evaluate,← H.liftPoint_slice_image]
      exact ⟨mixedTuple x.val,x.property,rfl⟩
    · intro hb
      change mixedTuple b ∈ H.liftedSlice (p .rv) at hb
      rw [← H.liftPoint_slice_image] at hb
      obtain ⟨q,hq,e⟩ := hb
      obtain ⟨a,rfl⟩ := mixedTuple_surjective q
      exact ⟨⟨a,hq⟩,mixedTuple_injective ((evaluate ⟨a,hq⟩).trans e)⟩
  have iso : MixedGraphIso M T source (Set.range f) := MixedGraphIso.toRange f inj fDef
  have iso' : MixedGraphIso M T source target := range ▸ iso
  exact ⟨iso'⟩

theorem head_slices_equivalent (J : HeadContractionData A)
    (p : SortedAssignment (CanonicalSort O) (RVVariables (Fin k))) :
    MixedDefinablyEquivalent M (M.termGenerated (namedTuple S p))
      {a : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) H.target.tags) | mixedTuple a ∈ H.liftedSlice (p .rv)}
      {b : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) J.target.tags) | mixedTuple b ∈ J.liftedSlice (p .rv)} := by
  obtain ⟨f⟩ := H.liftedSlice_equivalence p
  obtain ⟨g⟩ := J.liftedSlice_equivalence p
  let := A.finiteTags
  exact (f.symm.trans g).equivalent

theorem head_slices_equivalent_of_source_equiv {B : RetainedFieldFamily M S (n+1) k}
    (J : HeadContractionData B) (p : SortedAssignment (CanonicalSort O) (RVVariables (Fin k)))
    (e : MixedDefinablyEquivalent M (M.termGenerated (namedTuple S p))
      {a : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) A.tags) | mixedTuple a ∈ A.selectedFiber (p .rv)}
      {b : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) B.tags) | mixedTuple b ∈ B.selectedFiber (p .rv)}) :
    MixedDefinablyEquivalent M (M.termGenerated (namedTuple S p))
      {a : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) H.target.tags) | mixedTuple a ∈ H.liftedSlice (p .rv)}
      {b : SortedAssignment (CanonicalSort O) (MixedVariables (n+1) J.target.tags) | mixedTuple b ∈ J.liftedSlice (p .rv)} := by
  obtain ⟨f⟩ := H.liftedSlice_equivalence p
  obtain ⟨g⟩ := J.liftedSlice_equivalence p
  obtain ⟨mid,defMid⟩ := e
  let := A.finiteTags
  let := B.finiteTags
  exact ((f.symm.trans ⟨mid,defMid⟩).trans g).equivalent

end HeadContractionData

end GeneralizedEuler.Section5
