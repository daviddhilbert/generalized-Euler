module

public import Section5.PositionedHeadFamilies
public import Section5.TaggedTwoCellGeometry
public import Section5.PartialFieldFunctions
public import Section5.FieldOrderIsomorphisms

/-! A vertical head preparation, with its history recorded and the
fields unchanged, gives a fixed-base positioned family. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem positioned_annotation_from_head
    (head : HeadPreparationHypotheses O hO power S) (default : S.carrier .vf)
    (A : RetainedFieldFamily 𝓜 S 2 k) (H : HeadContractionData (n := 1) A) :
    let A' := A.permuteVF (Equiv.swap 0 1)
    ∃ (B : RetainedFieldFamily 𝓜 S 2 k) (_ : TaggedPositioningData B)
      (e : MixedGraphIso 𝓜 S
        {a : SortedAssignment Z (MixedVariables 2 A'.tags) | mixedTuple a ∈ A'.carrier}
        {b : SortedAssignment Z (MixedVariables 2 B.tags) | mixedTuple b ∈ B.carrier}),
      (∀ a, (e.equiv a).val .vf = a.val .vf) ∧
      (∀ a, (e.equiv a).val .rv ∘ B.select = a.val .rv ∘ A'.select) := by
  intro A'
  let swap := Equiv.swap (0 : Fin 2) 1
  let B := H.recordedFamily.permuteVF swap
  let T := HistoryIndex H.length ⊕ A.tags
  let U := MixedVariables 1 T
  let F (a : SortedAssignment Z U) (v : fieldAssignment 1 Z) :=
    mixedTuple a ∈ H.target.carrier ∧ H.recordedCenter (a .vf) (a .rv) = v .vf 0
  have graph : DefinableRelation 𝓜 S.carrier F := H.recordedCenter_graph O hO power S head.fieldTerms
    head.minusOne head.minusOne_realizes head.fieldTerms_realize
  have unique (a b c) (hb : F a b) (hc : F a c) : b = c := by
    apply fieldAssignment_ext
    intro i
    rw [Fin.eq_zero i]
    exact hb.2.symm.trans hc.2
  obtain ⟨value,eval,defValue⟩ := definable_partial_field_function F graph unique default
  let p (x : K) (q : T → RV0 O) := value (mixedAssignment (fun _ => x) q)
  let t (q : T → RV0 O) := q (.inl (lastIndex H.length))
  have peval (x : K) (q : T → RV0 O) (hx : ((fun _ : Fin 1 => x),q) ∈ H.target.carrier) :
      p x q = H.recordedCenter (fun _ => x) q := by
    let y : fieldAssignment 1 Z := fieldTupleAssignment (fun _ => H.recordedCenter (fun _ => x) q)
    exact eval (mixedAssignment (fun _ => x) q) y ⟨hx,rfl⟩
  have positionDef : DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment Z U) (b : fieldAssignment 1 Z) => p (a .vf 0) (a .rv) = b .vf 0) := by
    apply defValue.congr
    intro a b
    have field : (fun _ : Fin 1 => a .vf 0) = a .vf := by funext i; rw [Fin.eq_zero i]
    change value a = b .vf 0 ↔ value (mixedAssignment (fun _ => a .vf 0) (a .rv)) = b .vf 0
    rw [field,mixedAssignment_eta]
  have paradigmDef : DefinableRelation 𝓜 S.carrier (fun
      (a : SortedAssignment Z (RVVariables T)) (b : SortedAssignment Z (RVVariables (Fin 1))) =>
        t (a .rv) = b .rv 0) :=
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier)
      (Var := SumVariables (RVVariables T) (RVVariables (Fin 1))) .rv (.inl (.inl (lastIndex H.length))) (.inr 0)
  have pair (q : T → RV0 O) (x y : K) :
      (x,y) ∈ B.pairFiber q ↔ (y,(fun _ => x),q) ∈ H.recordedFamily.verticalCarrier := by
    let fields : Fin 2 → K := Fin.cases x (fun _ => y)
    have e : fields ∘ swap.symm = Fin.cons y (fun _ => x) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change fields (swap 0) = y
        rw [show swap 0 = 1 from Equiv.swap_apply_left _ _]
        rfl
      · rw [Fin.eq_zero j]
        change fields (swap 1) = x
        rw [show swap 1 = 0 from Equiv.swap_apply_right _ _]
        rfl
    change (fields ∘ swap.symm,q) ∈ H.recordedFamily.carrier ↔
      (Fin.cons y (fun _ => x),q) ∈ H.recordedFamily.carrier
    rw [e]
  have domain (q : T → RV0 O) (x : K) : x ∈ B.firstDomain q ↔ ((fun _ : Fin 1 => x),q) ∈ H.target.carrier := by
    refine (B.firstDomain_iff_pair q x).trans ?_
    constructor
    · rintro ⟨y,hy⟩
      exact ((H.recordedFamily_position (fun _ => x) q y).1 ((pair q x y).1 hy)).1
    · intro hx
      obtain ⟨y,hy⟩ := rv_surjective O (t q)
      let r := H.recordedCenter (fun _ => x) q
      refine ⟨y+r,(pair q x _).2 ((H.recordedFamily_position (fun _ => x) q _).2 ⟨hx,?_⟩)⟩
      change rv O (y+r-r) = t q
      rwa [add_sub_cancel_right]
  have shapes (q : T → RV0 O) : B.pairFiber q = positionedCell O (B.firstDomain q) (fun x => p x q) (t q) := by
    ext z
    refine (pair q z.1 z.2).trans ((H.recordedFamily_position _ q _).trans ?_)
    change (((fun _ : Fin 1 => z.1),q) ∈ H.target.carrier ∧
      rv O (z.2-H.recordedCenter (fun _ => z.1) q) = t q) ↔
      z.1 ∈ B.firstDomain q ∧ rv O (z.2-p z.1 q) = t q
    constructor
    · rintro ⟨h,he⟩
      exact ⟨(domain q z.1).2 h,by rw [peval z.1 q h]; exact he⟩
    · rintro ⟨h,he⟩
      have h' := (domain q z.1).1 h
      exact ⟨h',by rw [← peval z.1 q h']; exact he⟩
  let data : TaggedPositioningData B :=
    { position := p
      paradigm := t
      positionDef := positionDef
      paradigmDef := paradigmDef
      shapes := shapes }
  obtain ⟨e,fix,keep⟩ := A.withRecordedLabels_iso H.historyCode H.historyCode_graph
  obtain ⟨e',eval⟩ := RetainedFieldFamily.permuted_iso (A := A) (B := H.recordedFamily) e swap
  let first := (A.permuteVF_iso swap).choose
  refine ⟨B,data,e',?_,?_⟩
  · intro a
    let x := first.equiv.symm a
    have ev := (A.permuteVF_iso swap).choose_spec.1 x
    have old : a.val .vf = x.val .vf ∘ swap :=
      (congrArg (fun u => u.val .vf) (first.equiv.apply_symm_apply a)).symm.trans ev
    exact (eval a).1.trans ((congrArg (· ∘ swap) (fix x)).trans old.symm)
  · intro a
    let x := first.equiv.symm a
    have ev := (A.permuteVF_iso swap).choose_spec.2 x
    have old : a.val .rv = x.val .rv :=
      (congrArg (fun u => u.val .rv) (first.equiv.apply_symm_apply a)).symm.trans ev
    exact (congrArg (· ∘ Sum.inr ∘ A.select) (eval a).2).trans
      (congrArg (· ∘ A.select) ((keep x).trans old.symm))

end GeneralizedEuler.Section5
