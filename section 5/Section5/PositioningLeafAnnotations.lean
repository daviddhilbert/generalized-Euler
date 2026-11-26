module

public import Section5.PositioningLeafLabelFunctions
public import Section5.PositioningLeafSemantics
public import Section5.RecordedFieldLabels
public import Section5.TagRestrictedContractions

/-! Recording a valid unary leaf label turns the positioned
family over that parameter part into a tagged two-cell family.
The annotation retains the field coordinates and all old labels. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)} {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty

namespace TaggedPositioningData

variable {A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 2 k}
  (C : TaggedPositioningData A)

theorem leaf_annotation
    (part : Set (A.tags → RV0 O)) (defPart : isRVSet 𝓜 S part)
    (W : PositioningLeafScheme 𝓜 S (RVVariables A.tags))
    (valid : ∀ q ∈ part, W.valid O hO power S A.positioningDomainScheme C.graphScheme (rvAssignment q)) :
    let A₀ := A.restrictTags part defPart
    ∃ (B : RetainedFieldFamily 𝓜 S 2 k) (_ : TaggedTwoCellGeometry B)
      (e : MixedGraphIso 𝓜 S
        {a : SortedAssignment Z (MixedVariables 2 A₀.tags) | mixedTuple a ∈ A₀.carrier}
        {b : SortedAssignment Z (MixedVariables 2 B.tags) | mixedTuple b ∈ B.carrier}),
      (∀ a, (e.equiv a).val .vf = a.val .vf) ∧
      (∀ a, (e.equiv a).val .rv ∘ B.select = a.val .rv ∘ A₀.select) := by
  intro A₀
  let T := Fin W.arity ⊕ A.tags
  let R := RVVariables (Fin W.arity)
  obtain ⟨label,defLabel,reads⟩ := C.leaf_label_function W part defPart valid
  let B := A₀.withRecordedLabels label defLabel
  let fields (x y : K) : Fin 2 → K := Fin.cases x (fun _ => y)
  let leaf (q : T → RV0 O) (x : K) :
      SortedAssignment Z (SumVariables (SumVariables (RVVariables A.tags) R) U) :=
    appendAssignments (appendAssignments (rvAssignment (q ∘ Sum.inr))
      (rvAssignment (q ∘ Sum.inl))) (fieldTupleAssignment (fun _ => x))
  let D (q : T → RV0 O) : Set K := {x | q ∘ Sum.inr ∈ part ∧ leaf q x ∈ W.leaves}
  have oldDomain (q : T → RV0 O) (x : K) (h : x ∈ D q) : x ∈ A.firstDomain (q ∘ Sum.inr) :=
    ((valid (q ∘ Sum.inr) h.1).1 (fieldTupleAssignment (fun _ => x))).2
      ⟨rvAssignment (q ∘ Sum.inl),h.2⟩
  let f (x : K) (q : T → RV0 O) := C.position x (q ∘ Sum.inr)
  let t (q : T → RV0 O) := C.paradigm (q ∘ Sum.inr)
  have pair (q : T → RV0 O) (x y : K) :
      (x,y) ∈ B.pairFiber q ↔
        x ∈ D q ∧ rv O (y-f x q) = t q := by
    let a : SortedAssignment Z (MixedVariables 2 T) := mixedAssignment (fields x y) q
    let old : SortedAssignment Z (MixedVariables 2 A.tags) := mixedAssignment (fields x y) (q ∘ Sum.inr)
    have mem : (x,y) ∈ B.pairFiber q ↔
        (((x,y) ∈ A.pairFiber (q ∘ Sum.inr)) ∧ q ∘ Sum.inr ∈ part) ∧ label old = q ∘ Sum.inl := by
      exact A₀.recordedCarrier_mem label a
    have look (h : q ∘ Sum.inr ∈ part) (hx : x ∈ A.firstDomain (q ∘ Sum.inr)) :
        label old = q ∘ Sum.inl ↔ leaf q x ∈ W.leaves :=
      reads old (rvAssignment (q ∘ Sum.inl)) h hx
    have raw : (x,y) ∈ A.pairFiber (q ∘ Sum.inr) ↔
        x ∈ A.firstDomain (q ∘ Sum.inr) ∧ rv O (y-f x q) = t q := by
      rw [C.shapes]
      rfl
    constructor
    · intro h
      obtain ⟨⟨m,part⟩,r⟩ := mem.1 h
      obtain ⟨xD,e⟩ := raw.1 m
      exact ⟨⟨part,(look part xD).1 r⟩,e⟩
    · rintro ⟨d,e⟩
      have xD := oldDomain q x d
      exact mem.2 ⟨⟨raw.2 ⟨xD,e⟩,d.1⟩,(look d.1 xD).2 d.2⟩
  have domain (q : T → RV0 O) : B.firstDomain q = D q := by
    ext x
    refine (B.firstDomain_iff_pair q x).trans ?_
    constructor
    · rintro ⟨y,hy⟩
      exact ((pair q x y).1 hy).1
    · intro d
      obtain ⟨w,hw⟩ := rv_surjective O (t q)
      exact ⟨w+f x q,(pair q x _).2 ⟨d,by rwa [add_sub_cancel_right]⟩⟩
  have fg : DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment Z (MixedVariables 1 T)) (b : fieldAssignment 1 Z) => f (a .vf 0) (a .rv) = b .vf 0) := by
    let ren : (s : TCsort) → SumVariables (MixedVariables 1 A.tags) U s → SumVariables (MixedVariables 1 T) U s
      | .vf => id
      | .rv => Sum.elim (Sum.inl ∘ Sum.inr) Empty.elim
    have g := C.positionDef
    unfold DefinableRelation at g ⊢
    exact g.pullback_relabel ren
  have tg : DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment Z (RVVariables T)) (b : SortedAssignment Z (RVVariables (Fin 1))) => t (a .rv) = b .rv 0) := by
    let ren : (s : TCsort) → SumVariables (RVVariables A.tags) (RVVariables (Fin 1)) s →
      SumVariables (RVVariables T) (RVVariables (Fin 1)) s
      | .vf => id
      | .rv => Sum.map Sum.inr id
    have g := C.paradigmDef
    unfold DefinableRelation at g ⊢
    exact g.pullback_relabel ren
  have shapes (q : T → RV0 O) : B.pairFiber q = positionedCell O (B.firstDomain q) (fun x => f x q) (t q) := by
    rw [domain q]
    exact Set.ext (fun p => pair q p.1 p.2)
  have leaves (q : T → RV0 O) :
      (∀ x ∈ B.firstDomain q, ∀ y ∈ B.firstDomain q, f x q = f y q) ∨
        ∃ (a b : K) (r s : O.ValueGroup) (u : RV O), r ≠ 0 ∧ s ≠ 0 ∧
          B.firstDomain q = openDisc O a r ∧ (fun x => f x q) '' B.firstDomain q = openDisc O b s ∧
          RVAffineOn O (B.firstDomain q) (fun x => f x q) u := by
    rw [domain q]
    by_cases h : q ∘ Sum.inr ∈ part
    · let p : SortedAssignment Z (RVVariables A.tags) := rvAssignment (q ∘ Sum.inr)
      let r : SortedAssignment Z R := rvAssignment (q ∘ Sum.inl)
      have data := (valid (q ∘ Sum.inr) h).2.2 r
      apply positioningLeafValid.geometry O data (D q) (fun x => f x q)
      · intro x
        have field : fieldTupleAssignment (fun _ => x .vf 0) = x :=
          fieldAssignment_ext (fun i => by rw [Fin.eq_zero i]; rfl)
        change appendAssignments (appendAssignments p r) x ∈ W.leaves ↔
          q ∘ Sum.inr ∈ part ∧ appendAssignments (appendAssignments p r)
            (fieldTupleAssignment (fun _ => x .vf 0)) ∈ W.leaves
        rw [field]
        exact ⟨fun leaf => ⟨h,leaf⟩,And.right⟩
      · intro x y _
        rfl
    · exact Or.inl (fun x hx _ _ => (h hx.1).elim)
  let geom : TaggedTwoCellGeometry B :=
    { position := f
      paradigm := t
      positionDef := fg
      paradigmDef := tg
      shapes := shapes
      leaves := leaves }
  obtain ⟨e,fix,keep⟩ := A₀.withRecordedLabels_iso label defLabel
  exact ⟨B,geom,e,fix,fun a => congrArg (· ∘ A₀.select) (keep a)⟩

end TaggedPositioningData

end GeneralizedEuler.Section5
