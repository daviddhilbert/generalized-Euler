module

public import Section5.RVObjectLifts

/-! A definable finite-to-one active label graph gives an RV object
in its stated degree, with the original tuple as carrier. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {m k : ℕ}

namespace RVObject

variable (D : Set (Fin m → X .rv))
  (G : Set (SortedAssignment X (RVVariables (Fin m ⊕ Fin k))))
  (defD : isRVSet M S D) (defG : SortedDefinableOver M S.carrier G)

@[expose] def labelGraphTuple (u : Fin m → X .rv) (v : Fin k → X .rv) :
    SortedAssignment X (RVVariables (Fin m ⊕ Fin k))
  | .vf => PEmpty.elim
  | .rv => Sum.elim u v

theorem labelGraphTuple_eta (a : SortedAssignment X (RVVariables (Fin m ⊕ Fin k))) :
    labelGraphTuple (a .rv ∘ Sum.inl) (a .rv ∘ Sum.inr) = a := by
  funext s i
  cases s
  · exact i.elim
  · cases i <;> rfl

variable (total : ∀ u, u ∈ D ↔ ∃ v, labelGraphTuple u v ∈ G)
  (functional : ∀ u v w, labelGraphTuple u v ∈ G → labelGraphTuple u w ∈ G → v = w)

include total in
@[expose] def labelFromGraph (u : D) : Fin k → X .rv := ((total u.val).1 u.property).choose

theorem labelFromGraph_mem (u : D) : labelGraphTuple u.val (labelFromGraph D G total u) ∈ G :=
  ((total u.val).1 u.property).choose_spec

include functional in
theorem labelFromGraph_iff (u : D) (v : Fin k → X .rv) :
    labelFromGraph D G total u = v ↔ labelGraphTuple u.val v ∈ G := by
  constructor
  · rintro rfl
    exact labelFromGraph_mem D G total u
  · intro hv
    exact functional _ _ _ (labelFromGraph_mem D G total u) hv

include defG functional in
theorem labelFromGraph_definable :
    SortedDefinableOver M S.carrier (rvGraph (labelFromGraph D G total)) := by
  convert defG using 1
  ext a
  rw [← labelGraphTuple_eta a]
  change (∃ u : D, u.val = a .rv ∘ Sum.inl ∧
    labelFromGraph D G total u = a .rv ∘ Sum.inr) ↔
    labelGraphTuple (a .rv ∘ Sum.inl) (a .rv ∘ Sum.inr) ∈ G
  constructor
  · rintro ⟨u,hu,hv⟩
    exact hu ▸ (labelFromGraph_iff D G total functional u _).1 hv
  · intro hv
    let u : D := ⟨_,(total _).2 ⟨_,hv⟩⟩
    exact ⟨u,rfl,(labelFromGraph_iff D G total functional u _).2 hv⟩

/-- The graph describes both the carrier and the chosen label. -/
@[expose] def ofLabelGraph
    (nonzero : ∀ u v, labelGraphTuple u v ∈ G → ∀ j, v j ≠ M.funMap .rvZero (fun i => i.elim0))
    (finite : ∀ v, {u | labelGraphTuple u v ∈ G}.Finite) : RVObject M S k where
  arity := m
  carrier := D
  definable := defD
  label := labelFromGraph D G total
  graph := labelFromGraph_definable D G defG total functional
  nonzero u := nonzero u.val _ (labelFromGraph_mem D G total u)
  finiteFibers v := by
    apply ((finite v).preimage (Subtype.val_injective : Function.Injective (Subtype.val : D → _)).injOn).subset
    intro u hu
    exact (labelFromGraph_iff D G total functional u v).1 hu

end RVObject

end GeneralizedEuler.Section5
