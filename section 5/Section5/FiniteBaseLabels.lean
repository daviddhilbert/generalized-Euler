module

public import Section5.LiftBoundaryDimension
public import Section4.BaseAndDimension

/-! Every point of a finite RV set over an elementary base has field
representatives in the base under Hypothesis 5.11. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} (S : SortedSubstructure M) {n : ℕ}

private theorem rvTuple_ext {a b : labelAssignment n X} (h : a .rv = b .rv) : a = b := by
  funext s i
  cases s with
  | vf => exact i.elim
  | rv => exact congrFun h i

theorem definable_base_label (a : labelAssignment n X)
    (h : ∀ i, a .rv i ∈ S.carrier .rv) :
    SortedDefinableOver M S.carrier ({a} : Set (labelAssignment n X)) := by
  have hj (i : Fin n) := SortedDefinableOver.coordinate_eq_parameter
    (M := M) (A := S.carrier) (Var := RVVariables (Fin n)) .rv i ⟨a .rv i,h i⟩
  convert SortedDefinableOver.iInter hj using 1
  ext b
  simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨fun he i => congrFun (congrFun he .rv) i, fun ht => rvTuple_ext (funext ht)⟩

/-- Remove the finite list of already named points. If anything remains,
elementarity would supply a named point in the remainder. -/
theorem finite_definable_labels_in_base
    (elem : ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → S.carrier s),
      φ.realize S.structureOn v ↔ φ.realize M (fun s => Subtype.val ∘ v s))
    (A : Set (labelAssignment n X)) (hA : SortedDefinableOver M S.carrier A)
    (finiteA : A.Finite) :
    ∀ a ∈ A, ∀ i, a .rv i ∈ S.carrier .rv := by
  let named := {a ∈ A | ∀ i, a .rv i ∈ S.carrier .rv}
  have hf : named.Finite := finiteA.subset (fun _ h => h.1)
  let : Finite named := hf.to_subtype
  have hNamed : SortedDefinableOver M S.carrier named := by
    have h := SortedDefinableOver.iUnion
      (fun a : named => definable_base_label S a.val a.property.2)
    convert h using 1
    ext a
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨fun ha => ⟨⟨a,ha⟩,rfl⟩, fun ⟨b,he⟩ => he.symm ▸ b.property⟩
  have hRest := hA.inter hNamed.compl
  let R : Set (Fin n → X .rv) := rvTupleAssignment ⁻¹' (A ∩ namedᶜ)
  have hR : isRVSet M S R := by
    unfold isRVSet
    convert hRest using 1
    ext a
    change rvTupleAssignment (a .rv) ∈ A ∩ namedᶜ ↔ a ∈ A ∩ namedᶜ
    rw [rvTuple_ext (a := rvTupleAssignment (a .rv)) (b := a) rfl]
  intro a ha
  by_contra hn
  have hn' : a ∉ named := fun h => hn h.2
  have hne : R.Nonempty := ⟨a .rv,by
    change rvTupleAssignment (a .rv) ∈ A ∩ namedᶜ
    rw [rvTuple_ext (a := rvTupleAssignment (a .rv)) (b := a) rfl]
    exact ⟨ha,hn'⟩⟩
  obtain ⟨x,hx,hBase⟩ := rv_base_witness M S S (fun _ _ h => h) (fun _ h => h) elem hR hne
  exact hx.2 ⟨hx.1,hBase⟩

/-- Each coordinate of a finite RV set has a representative in the VF
sort of the original base. -/
theorem finite_definable_labels_represented
    (elem : ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → S.carrier s),
      φ.realize S.structureOn v ↔ φ.realize M (fun s => Subtype.val ∘ v s))
    (generated : S.structureOn.IsVFGenerated)
    (A : Set (labelAssignment n X)) (hA : SortedDefinableOver M S.carrier A)
    (finiteA : A.Finite) :
    ∃ repr : A → Fin n → S.carrier .vf,
      ∀ a i, M.rvMap (repr a i).val = a.val .rv i := by
  have contains := finite_definable_labels_in_base S elem A hA finiteA
  have atCoord (a : A) (i : Fin n) :
      ∃ x : S.carrier .vf, M.rvMap x.val = a.val .rv i := by
    obtain ⟨x,hx⟩ := generated ⟨a.val .rv i,contains a.val a.property i⟩
    have he := S.inclusion.map_rv x
    rw [hx] at he
    refine ⟨x,?_⟩
    simpa only [SortedSubstructure.inclusion_apply] using he.symm
  choose repr h using atCoord
  exact ⟨repr,h⟩

end GeneralizedEuler.Section5
