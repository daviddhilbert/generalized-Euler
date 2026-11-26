module

public import Section5.VerticalContractionFiniteness
public import Section5.PreparedMaps

/-! Contract the first field coordinate by recording its history.
The remaining field tuple and all old RV tags stay in the carrier. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K)
  {n ℓ : ℕ} {I : Type}

local notation "H" => HistoryIndex ℓ
local notation "Prep" => UnaryPreparation O (PreparationLabels O (RV0 O) ℓ)
local notation "Domain" => Set (K × ((Fin n → K) × (I → RV0 O)))
local notation "Y" => CanonicalSort O

@[expose] def contractedVerticalSet (P : (Fin n → K) → Prep) (A : Domain) :
    Set (PreparationPoint O (Fin n) (H ⊕ I)) :=
  {v | ∃ x, (x,v.1,v.2 ∘ Sum.inr) ∈ A ∧
    (P v.1).label x = decodeHistory O ℓ (v.2 ∘ Sum.inl)}

variable {L : Language} {E : Type*} {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}

theorem contractedVerticalSet_definable
    (P : (Fin n → K) → Prep) (A : Domain)
    (defA : SortedDefinableOver M S.carrier
      {a : SortedAssignment Y (VerticalVariables n I) | (a .vf (.inl ()),a .vf ∘ Sum.inr,a .rv) ∈ A})
    (defH : DefinableRelation M S.carrier (fun (a : SortedAssignment Y (VerticalVariables n I))
      (v : SortedAssignment Y (RVVariables H)) =>
      (P (a .vf ∘ Sum.inr)).label (a .vf (.inl ())) = decodeHistory O ℓ (v .rv))) :
    SortedDefinableOver M S.carrier
      {v : SortedAssignment Y (MixedVariables n (H ⊕ I)) | mixedTuple v ∈ contractedVerticalSet O P A} := by
  let W := MixedVariables n (H ⊕ I)
  let T := SumVariables W (MixedVariables 1 Empty)
  let take : (s : TCsort) → VerticalVariables n I s → T s
    | .vf => Sum.elim (fun _ => .inr 0) Sum.inl
    | .rv => Sum.inl ∘ Sum.inr
  let lab : (s : TCsort) → RVVariables H s → T s
    | .vf => PEmpty.elim
    | .rv => Sum.inl ∘ Sum.inl
  let rename (s : TCsort) : SumVariables (VerticalVariables n I) (RVVariables H) s → T s := Sum.elim (take s) (lab s)
  unfold DefinableRelation at defH
  have raw := definable_project_mixed ((defA.pullback_relabel take).inter (defH.pullback_relabel rename))
  convert raw using 1
  ext v
  let b := v .vf
  let a := v .rv ∘ Sum.inr
  let h := decodeHistory O ℓ (v .rv ∘ Sum.inl)
  change (∃ x, (x,b,a) ∈ A ∧ (P b).label x = h) ↔
    ∃ x : fieldAssignment 1 Y, (x .vf 0,b,a) ∈ A ∧ (P b).label (x .vf 0) = h
  exact ⟨fun ⟨x,hx,e⟩ => ⟨fieldTupleAssignment (fun _ => x),hx,e⟩,fun ⟨x,hx,e⟩ => ⟨x .vf 0,hx,e⟩⟩

theorem contractedVerticalSet_selected_finite {k : ℕ}
    (P : (Fin n → K) → Prep) (A : Domain)
    (select : Fin k → I) (last : H)
    (lead : ∀ b h, (P b).lead (decodeHistory O ℓ h) = h last)
    (finiteOffsets : ∀ b, (Set.range (P b).offset).Finite)
    (finite : ∀ x b (r : Fin k → RV0 O), {t : I → RV0 O | (x,b,t) ∈ A ∧ t ∘ select = r}.Finite)
    (constant : ∀ b x y t, (P b).label x = (P b).label y → ((x,b,t) ∈ A ↔ (y,b,t) ∈ A)) :
    ∀ b (u : RV0 O) (r : Fin k → RV0 O),
      {t : H ⊕ I → RV0 O | (b,t) ∈ contractedVerticalSet O P A ∧
        t (.inl last) = u ∧ t ∘ Sum.inr ∘ select = r}.Finite := by
  intro b u r
  have f := vertical_contracted_labels_finite_over_selected O A P (fun t => t ∘ select)
    finite finiteOffsets constant b u r
  let project (t : H ⊕ I → RV0 O) : PreparationLabels O (RV0 O) ℓ × (I → RV0 O) :=
    (decodeHistory O ℓ (t ∘ Sum.inl),t ∘ Sum.inr)
  have inj : Function.Injective project := by
    intro s t eq
    have h := congrArg (encodeHistory O ℓ) (congrArg Prod.fst eq)
    change encodeHistory O ℓ (decodeHistory O ℓ (s ∘ Sum.inl)) =
      encodeHistory O ℓ (decodeHistory O ℓ (t ∘ Sum.inl)) at h
    rw [encode_decode_history,encode_decode_history] at h
    funext i
    rcases i with i | i
    · exact congrFun h i
    · exact congrFun (congrArg Prod.snd eq) i
  apply (f.preimage inj.injOn).subset
  rintro t ⟨ht,hu,hr⟩
  exact ⟨ht,(lead b (t ∘ Sum.inl)).trans hu,hr⟩

end GeneralizedEuler.Section5
