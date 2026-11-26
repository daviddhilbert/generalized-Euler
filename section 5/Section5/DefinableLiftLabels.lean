module

public import Section5.ElementaryFieldChoice
public import Section3.Contraction

/-! The leading-term relation and the boundary of a VF set over a fixed base. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {n : ℕ}

abbrev labelAssignment (n : ℕ) (X : TCsort → Type z) :=
  SortedAssignment X (RVVariables (Fin n))

/-- Apply the leading-term function to each field coordinate. -/
@[expose] def fieldLead (M : SortedStructure L E X) (a : fieldAssignment n X) :
    labelAssignment n X
  | .vf => PEmpty.elim
  | .rv => M.rvMap ∘ a .vf

theorem fieldLead_surjective (h : Function.Surjective M.rvMap) :
    Function.Surjective (fieldLead M (n := n)) := by
  intro b
  choose a ha using fun i : Fin n => h (b .rv i)
  let x : fieldAssignment n X
    | .vf => a
    | .rv => Empty.elim
  refine ⟨x,?_⟩
  funext s i
  cases s with
  | vf => exact i.elim
  | rv => exact ha i

theorem fieldLead_definable :
    DefinableRelation M S.carrier
      (fun x : fieldAssignment n X => fun y => fieldLead M x = y) := by
  let V := SumVariables (MixedVariables n Empty) (RVVariables (Fin n))
  let lead (i : Fin n) : SortedTerm L E (WithBase S.carrier V) .rv :=
    rvOfVF (.var (.inr (.inl i)))
  have h := SortedDefinableOver.iInter (fun i : Fin n =>
    SortedDefinableOver.coordinate_eq_term (M := M) (A := S.carrier) (Var := V)
      .rv (.inr i) (lead i))
  unfold DefinableRelation
  convert h using 1
  ext a
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, lead, rvOfVF, SortedTerm.realize, M.funMap_rv]
  constructor
  · intro eq i
    exact (congrFun (congrFun eq .rv) i).symm
  · intro eq
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => exact (eq i).symm

theorem rvBoundary_eq_image_inter {A B : Type*} (p : A → B) (D : Set A) :
    rvBoundary p D = p '' D ∩ p '' Dᶜ := by
  ext b
  constructor
  · rintro ⟨h,x,hx,hD⟩
    exact ⟨h, x, hD, hx⟩
  · rintro ⟨h,x,hD,hx⟩
    exact ⟨h, x, hx, hD⟩

theorem definable_fieldLead_image {D : Set (fieldAssignment n X)}
    (hD : SortedDefinableOver M S.carrier D) :
    SortedDefinableOver M S.carrier (fieldLead M '' D) := by
  exact (fieldLead_definable (S := S)).image hD

theorem definable_fieldLead_preimage {D : Set (labelAssignment n X)}
    (hD : SortedDefinableOver M S.carrier D) :
    SortedDefinableOver M S.carrier (fieldLead M ⁻¹' D) := by
  have h := (fieldLead_definable (S := S)).transpose.image hD
  convert h using 1
  ext a
  change fieldLead M a ∈ D ↔ ∃ b ∈ D, fieldLead M a = b
  exact ⟨fun ha => ⟨_,ha,rfl⟩, fun ⟨_,hb,he⟩ => he ▸ hb⟩

theorem definable_fieldLead_boundary {D : Set (fieldAssignment n X)}
    (hD : SortedDefinableOver M S.carrier D) :
    SortedDefinableOver M S.carrier (rvBoundary (fieldLead M) D) := by
  rw [rvBoundary_eq_image_inter]
  exact (definable_fieldLead_image hD).inter (definable_fieldLead_image hD.compl)

end GeneralizedEuler.Section5
