module

public import Section5.HeadContractionSlices
public import Section5.UnaryLabelObjects
public import Section5.PairedUnaryGraphs
public import Section5.EncodedTranslationLabels

/-! Over a fixed old RV tuple, a unary head contraction is a full
pullback with finite field fibers. Its RV label records precisely
the contracted tags and the new selected leading term. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {k : ℕ}
  {A : RetainedFieldFamily M S 1 k}

namespace HeadContractionData

variable (H : HeadContractionData (n := 0) A)

@[expose] def unarySlice (v : Fin k → RV0 O) : Set (K × (H.target.tags → RV0 O)) :=
  {p | (Fin.elim0,p.2) ∈ H.target.carrier ∧
    p.2 ∘ H.target.select ∘ Fin.castSucc = v ∧ rv O p.1 = p.2 (H.target.select (Fin.last k))}

theorem unarySlice_pullback (v : Fin k → RV0 O) : IsUnaryPullback O (H.unarySlice v) := by
  rintro x ⟨hx,old,new⟩ y e
  have h := congrArg Prod.fst e
  have t := congrArg Prod.snd e
  change rv O x.1 = rv O y.1 at h
  change x.2 = y.2 at t
  exact ⟨t ▸ hx,t ▸ old,t ▸ (h.symm.trans new)⟩

theorem unarySlice_finite (v : Fin k → RV0 O) : UnaryFiniteFibers (H.unarySlice v) := by
  intro x
  let labels : Fin (k+1) → RV0 O := Fin.lastCases (rv O x) v
  apply (H.target.finiteFibers Fin.elim0 labels).subset
  rintro q ⟨hq,old,new⟩
  refine ⟨hq,funext (Fin.lastCases ?_ (fun i => ?_))⟩
  · simpa only [Function.comp_apply,labels,Fin.lastCases_last] using new.symm
  · simpa only [Function.comp_apply,labels,Fin.lastCases_castSucc] using congrFun old i

theorem unarySlice_iff_liftedSlice (v : Fin k → RV0 O)
    (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 H.target.tags)) :
    unaryPair O a ∈ H.unarySlice v ↔ mixedTuple a ∈ H.liftedSlice v := by
  have emptyTail : a .vf ∘ Fin.succ = (Fin.elim0 : Fin 0 → K) := Subsingleton.elim _ _
  have last : H.target.select (Fin.last k) = Sum.inl (lastIndex H.length) := by
    simp only [HeadContractionData.target,Fin.lastCases_last]
  change ((Fin.elim0,a .rv) ∈ H.target.carrier ∧ a .rv ∘ H.target.select ∘ Fin.castSucc = v ∧
    rv O (a .vf 0) = a .rv (H.target.select (Fin.last k))) ↔
    (((a .vf ∘ Fin.succ,a .rv) ∈ H.target.carrier ∧ rv O (a .vf 0) = a .rv (.inl (lastIndex H.length))) ∧
    a .rv ∘ H.target.select ∘ Fin.castSucc = v)
  rw [emptyTail,last]
  exact ⟨fun ⟨h,o,l⟩ => ⟨⟨h,l⟩,o⟩,fun ⟨⟨h,l⟩,o⟩ => ⟨h,o,l⟩⟩

theorem unarySlice_definable (p : SortedAssignment (CanonicalSort O) (RVVariables (Fin k))) :
    SortedDefinableOver M (M.termGenerated (namedTuple S p)).carrier
      {a : SortedAssignment (CanonicalSort O) (MixedVariables 1 H.target.tags) |
        unaryPair O a ∈ H.unarySlice (p .rv)} := by
  obtain ⟨e⟩ := H.liftedSlice_equivalence p
  let := A.finiteTags
  convert e.target_definable (A.selectedFiber_definable p) using 1
  ext a
  exact H.unarySlice_iff_liftedSlice (p .rv) a

theorem unarySlice_labelSet (v : Fin k → RV0 O) {m : ℕ} (idx : Fin m ≃ Fin 1 ⊕ H.target.tags) :
    reindexedUnaryLabels O (H.unarySlice v) idx =
      {u | let tags := u ∘ idx.symm ∘ Sum.inr
           (Fin.elim0,tags) ∈ H.target.carrier ∧ tags ∘ H.target.select ∘ Fin.castSucc = v ∧
           u (idx.symm (.inl 0)) = tags (H.target.select (Fin.last k))} := by
  ext u
  let r := u ∘ idx.symm
  let tags := r ∘ Sum.inr
  let pulse := r (.inl 0)
  change r ∈ unaryLabelSet O (H.unarySlice v) ↔ _
  rw [unaryLabelSet_iff_decoded]
  constructor
  · rintro ⟨x,hx,e⟩
    have sameTags : x.2 = tags := congrArg Prod.snd e
    have h : rv O x.1 = pulse := congrArg Prod.fst e
    change (Fin.elim0,tags) ∈ H.target.carrier ∧ tags ∘ H.target.select ∘ Fin.castSucc = v ∧
      pulse = tags (H.target.select (Fin.last k))
    rw [← sameTags]
    exact ⟨hx.1,hx.2.1,h.symm.trans hx.2.2⟩
  · rintro ⟨ht,old,new⟩
    obtain ⟨x,hx⟩ := rv_surjective O pulse
    exact ⟨(x,tags),⟨ht,old,hx.trans new⟩,Prod.ext hx rfl⟩

end HeadContractionData

end GeneralizedEuler.Section5
