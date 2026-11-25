module

public import Section2.RVFormulaSeparation

/-! Functional graphs between the value and residue factors, as in
Lemma 2.23. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z u' v' u'' v''

variable {G H : Type*}

/-- Evaluate the two coordinates at a chosen representative of the
value and at a unit-valued residue element. -/
@[expose]
def valueResidueGraphCoordinates (oneG : G) (oneH : H) (x : G × H) : SplitAssignment G H Bool :=
  (fun b => if b then oneG else x.1, fun b => if b then x.2 else oneH)

theorem finite_range_of_separated_value_graph {A : Set (Bool → G) → Prop}
    {B : Set (Bool → H) → Prop} {D : Set (SplitAssignment G H Bool)}
    (hD : SeparatedSets A B D) (oneG : G) (oneH : H) (f : G → H)
    (hgraph : ∀ x y, valueResidueGraphCoordinates oneG oneH (x, y) ∈ D ↔ f x = y) :
    (Set.range f).Finite := by
  let slice := valueResidueGraphCoordinates oneG oneH ⁻¹' D
  have hslice : SeparatedSets (fun _ => True) (fun _ => True) slice :=
    SeparatedSets.preimage (fun x b => if b then oneG else x)
      (fun y b => if b then y else oneH) (fun _ => trivial) (fun _ => trivial) hD
  have hf := hslice.finite_snd_of_functional (by
    intro x y y' h h'
    exact ((hgraph x y).mp h).symm.trans ((hgraph x y').mp h'))
  convert hf using 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x, f x), (hgraph _ _).mpr rfl, rfl⟩
  · rintro ⟨⟨x, z⟩, hz, rfl⟩
    exact ⟨x, (hgraph _ _).mp hz⟩

theorem finite_range_of_separated_residue_graph {A : Set (Bool → G) → Prop}
    {B : Set (Bool → H) → Prop} {D : Set (SplitAssignment G H Bool)}
    (hD : SeparatedSets A B D) (oneG : G) (oneH : H) (f : H → G)
    (hgraph : ∀ x y, valueResidueGraphCoordinates oneG oneH (x, y) ∈ D ↔ f y = x) :
    (Set.range f).Finite := by
  let slice := valueResidueGraphCoordinates oneG oneH ⁻¹' D
  have hslice : SeparatedSets (fun _ => True) (fun _ => True) slice :=
    SeparatedSets.preimage (fun x b => if b then oneG else x)
      (fun y b => if b then y else oneH) (fun _ => trivial) (fun _ => trivial) hD
  have hf := hslice.finite_fst_of_functional (by
    intro x x' y h h'
    exact ((hgraph x y).mp h).symm.trans ((hgraph x' y).mp h'))
  convert hf using 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(f y, y), (hgraph _ _).mpr rfl, rfl⟩
  · rintro ⟨⟨z, y⟩, hz, rfl⟩
    exact ⟨y, (hgraph _ _).mp hz⟩

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {JG : Language.{u', v'}} {JH : Language.{u'', v''}} [JG.Structure G] [JH.Structure H]
  {A : Set G} {B : Set H} {M : SortedStructure L E X}
  (P : RVCoordinatePresentation M JG JH A B) (C : SortedSubstructure M)

/-- For a definable RV relation, substitute a value representative and
an embedded residue. If the resulting relation is functional in either
direction, its image is finite. -/
theorem finite_ranges_of_crossSortRVGraph (oneG : G) (oneH : H)
    {D : Set (Bool → X .rv)}
    (hD : SortedDefinableOver M C.carrier {x : ∀ s, RVVariables Bool s → X s | x .rv ∈ D})
    (hQE : ∀ φ : SortedFormula L E (FullRVVariables C Bool),
      ∃ q : SortedFormula L E (FullRVVariables C Bool), q.IsQF ∧
        ∀ v, q.realize M v ↔ φ.realize M v)
    (hparams : ∀ t : C.carrier .rv, (P.encode t.val).1 ∈ A ∧ (P.encode t.val).2 ∈ B)
    (hinput : ∀ i : Bool, SplitDefinable JG JH A B
      (splitTermGraph (fun x : SplitAssignment G H Bool => P.encode (P.decode (x.1 i, x.2 i)))))
    (relation : G → H → Prop)
    (hgraph : ∀ x y, (fun b => if b then P.decode (oneG, y) else P.decode (x, oneH)) ∈ D ↔ relation x y) :
    (∀ f : G → H, (∀ x y, relation x y ↔ f x = y) → (Set.range f).Finite) ∧
      (∀ f : H → G, (∀ x y, relation x y ↔ f y = x) → (Set.range f).Finite) := by
  have h := P.separated_rv_pullback (U := D) C hD hQE hparams hinput
  have eq (x : G) (y : H) :
      valueResidueGraphCoordinates oneG oneH (x, y) ∈
        {v : SplitAssignment G H Bool | (fun i => P.decode (v.1 i, v.2 i)) ∈ D} ↔ relation x y := by
    have he : (fun b : Bool => P.decode ((valueResidueGraphCoordinates oneG oneH (x, y)).1 b,
      (valueResidueGraphCoordinates oneG oneH (x, y)).2 b)) =
        (fun b => if b then P.decode (oneG, y) else P.decode (x, oneH)) := by
      funext b
      cases b <;> rfl
    change _ ∈ D ↔ _
    rw [he, hgraph]
  exact ⟨fun f hf => finite_range_of_separated_value_graph h oneG oneH f (fun x y => (eq x y).trans (hf x y)),
    fun f hf => finite_range_of_separated_residue_graph h oneG oneH f (fun x y => (eq x y).trans (hf x y))⟩

end GeneralizedEuler.Section2
