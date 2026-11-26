module

public import Section5.RelativeBlowupGraph
public import Section5.MultiCoordinateBlowup
public import Section5.ZeroBlowupObject

/-! The fixed-base graph of the lift of an elementary blowup on a
piece with injective deleted-label projection. -/

public section

noncomputable section

set_option autoImplicit false

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language
open ObjectLift (structureLabels structureLabels_definable)

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1)) (j : Fin (k+1))

abbrev ElementaryLiftVars (U : RVObject 𝓜 S (k+1)) :=
  MixedVariables (k+1) (Fin U.arity ⊕ Unit)

/-- Both multiplier strata in a single ambient field arity. At multiplier
zero the translated field coordinate is zero. -/
@[expose] def elementaryLiftCarrier (U : RVObject 𝓜 S (k+1)) (j : Fin (k+1)) :
    Set (SortedAssignment (CanonicalSort O) (ElementaryLiftVars O hO power S U)) :=
  {w | ∃ a : U.carrier, a.val = w .rv ∘ Sum.inl ∧
    unsignedValue O (w .rv (.inr ())) < 1 ∧
    ∀ i, rv O (w .vf i) = blowupLabel O j U.label (a,w .rv (.inr ())) i}

abbrev ElementaryLiftData (U : RVObject 𝓜 S (k+1)) (j : Fin (k+1)) :=
  Σ a : U.carrier, Σ s : BlowupMultiplier O,
    {y : Fin (k+1) → K // ∀ i, rv O (y i) = blowupLabel O j U.label (a,s.val) i}

private theorem subtype_heq_of_val_eq {X : Type*} {P Q : X → Prop}
    (h : P = Q) {x : Subtype P} {y : Subtype Q} (eq : x.val = y.val) : HEq x y := by
  subst Q
  exact heq_of_eq (Subtype.ext eq)

private def packElementaryPoint (p : ElementaryLiftData O hO power S U j) :
    elementaryLiftCarrier O hO power S U j := by
  let w : SortedAssignment (CanonicalSort O) (ElementaryLiftVars O hO power S U) :=
    fun s => match s with
    | .vf => p.2.2.val
    | .rv => Sum.elim p.1.val (fun _ => p.2.1.val)
  exact ⟨w,p.1,rfl,p.2.1.property,p.2.2.property⟩

private def packElementaryLift :
    ElementaryLiftData O hO power S U j ≃ elementaryLiftCarrier O hO power S U j := by
  apply Equiv.ofBijective (packElementaryPoint O hO power S U j)
  constructor
  · intro u v eq
    have value := congrArg Subtype.val eq
    have tag : u.1 = v.1 := Subtype.ext (funext fun i => congrFun (congrFun value .rv) (.inl i))
    cases u with
    | mk a u =>
      cases v with
      | mk b v =>
        change a = b at tag
        subst b
        have m : u.1 = v.1 := Subtype.ext (congrFun (congrFun value .rv) (.inr ()))
        apply congrArg (Sigma.mk a)
        refine Sigma.ext m (subtype_heq_of_val_eq ?_ (congrFun value .vf))
        exact congrArg (fun s : BlowupMultiplier O => fun y : Fin (k+1) → K =>
          ∀ i, rv O (y i) = blowupLabel O j U.label (a,s.val) i) m
  · intro w
    obtain ⟨a,ha,hm,hx⟩ := w.property
    refine ⟨⟨a,⟨w.val .rv (.inr ()),hm⟩,⟨w.val .vf,hx⟩⟩,?_⟩
    apply Subtype.ext
    funext s i
    cases s with
    | vf => rfl
    | rv => cases i with
      | inl i => exact congrFun ha i
      | inr i => cases i; rfl

private def unpackOriginalLift :
    ObjectLift.carrier U ≃
      Σ a : U.carrier, {x : Fin (k+1) → K // ∀ i, rv O (x i) = U.label a i} where
  toFun x := ⟨ObjectLift.tag U x,⟨x.val .vf,fun i => by
    simpa only [Function.comp_apply,canonicalStructure_rvMap] using
      (congrFun (ObjectLift.tag_label U x) i).symm⟩⟩
  invFun p := ObjectLift.assemble U p.1 p.2.val (by
    funext i
    rw [Function.comp_apply,canonicalStructure_rvMap]
    exact (p.2.property i).symm)
  left_inv x := ObjectLift.ext rfl (ObjectLift.assemble_tag U _ _ _)
  right_inv p := by
    obtain ⟨a,x⟩ := p
    refine Sigma.ext (ObjectLift.assemble_tag U _ _ _) (subtype_heq_of_val_eq ?_ rfl)
    exact congrArg (fun t : U.carrier => fun y : Fin (k+1) → K =>
      ∀ i, rv O (y i) = U.label t i) (ObjectLift.assemble_tag U _ _ _)

/-- An elementary blowup with injective retained projection preserves the
lift by a definable mixed bijection over the original two-sorted base. -/
theorem definable_elementary_lift_of_injective_projection
    (inj : Set.InjOn (projectLabels j.succAboveEmb) (structureLabels U))
    (sat : RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables k Empty))
      (BaseAssignments S.carrier (MixedVariables k Empty)))
    (elem : ∀ a : fieldAssignment k (CanonicalSort O),
      let B := (canonicalStructure (L := L) O hO power).termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → B.carrier s),
        φ.realize B.structureOn v ↔ φ.realize 𝓜 (fun s i => (v s i).val))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    ∃ e : ObjectLift.carrier U ≃ elementaryLiftCarrier O hO power S U j,
      (∀ a, (e a).val .rv ∘ Sum.inl = a.val .rv) ∧
      DefinableRelation 𝓜 S.carrier (fun
        (a : SortedAssignment (CanonicalSort O) (ObjectLift.Vars U))
        (b : SortedAssignment (CanonicalSort O) (ElementaryLiftVars O hO power S U)) =>
        ∃ ha : a ∈ ObjectLift.carrier U, (e ⟨a,ha⟩).val = b) := by
  let p := j.succAboveEmb
  let D := fieldLiftDomain 𝓜 (projectLabels p '' structureLabels U)
  have surj : Function.Surjective (canonicalStructure (L := L) O hO power).rvMap := by
    intro t
    obtain ⟨d,hd⟩ := rv_surjective O t
    exact ⟨d,(canonicalStructure_rvMap O hO power d).trans hd⟩
  obtain ⟨c,hc,cDef⟩ := definable_blowup_focus (S := S) p j inj
    surj sat elem (structureLabels_definable U)
  let original (a : U.carrier) (x : Fin (k+1) → K)
      (hx : ∀ i, rv O (x i) = U.label a i) : fieldLiftDomain 𝓜 (structureLabels U) :=
    ⟨fieldTupleAssignment x,⟨a,by
      funext s i
      cases s with
      | vf => exact i.elim
      | rv =>
        change U.label a i = (canonicalStructure (L := L) O hO power).rvMap (x i)
        rw [canonicalStructure_rvMap]
        exact (hx i).symm⟩⟩
  let retained (a : U.carrier)
      (v : {i : Fin (k+1) // i ≠ j} → K)
      (hv : ∀ i, rv O (v i) = U.label a i.val) : D :=
    ⟨fieldTupleAssignment (fun i => v ⟨p i,Fin.succAbove_ne j i⟩),
      ⟨rvTupleAssignment (U.label a),⟨a,rfl⟩,by
        funext s i
        cases s with
        | vf => exact i.elim
        | rv =>
          change U.label a (p i) = (canonicalStructure (L := L) O hO power).rvMap
            (v ⟨p i,Fin.succAbove_ne j i⟩)
          rw [canonicalStructure_rvMap]
          exact (hv ⟨p i,Fin.succAbove_ne j i⟩).symm⟩⟩
  let focus (a : U.carrier)
      (v : {v : {i : Fin (k+1) // i ≠ j} → K // ∀ i, rv O (v i) = U.label a i.val}) : K :=
    c (retained a v.val v.property)
  have focusLabel (a : U.carrier)
      (v : {v : {i : Fin (k+1) // i ≠ j} → K // ∀ i, rv O (v i) = U.label a i.val}) :
      rv O (focus a v) = U.label a j := by
    obtain ⟨d,hd⟩ := rv_surjective O (U.label a j)
    let x (i : Fin (k+1)) := if h : i ≠ j then v.val ⟨i,h⟩ else d
    have hx (i) : rv O (x i) = U.label a i := by
      by_cases h : i ≠ j
      · exact (congrArg (rv O) (dite_eq_left h)).trans (v.property ⟨i,h⟩)
      · have e : i = j := not_ne_iff.mp h
        exact (congrArg (rv O) (dite_eq_right h)).trans (e ▸ hd)
    have he : projectFieldLift p (original a x hx) = retained a v.val v.property := by
      apply Subtype.ext
      apply fieldAssignment_ext
      intro i
      exact dite_eq_left (Fin.succAbove_ne j i)
    have h := hc (original a x hx)
    rw [he] at h
    simp only [canonicalStructure_rvMap] at h
    exact h.trans (hx j)
  have focusNonzero (a) (v) : focus a v ≠ 0 := by
    intro h
    have he := focusLabel a v
    rw [h,map_zero] at he
    exact U.nonzero a j he.symm
  let e := (unpackOriginalLift O hO power S U).trans
    ((liftBlowupCoordinatesWithRelativeFocus O j U.label focus focusNonzero focusLabel).trans
      (packElementaryLift O hO power S U j))
  have oldTag (a : ObjectLift.carrier U) : (e a).val .rv ∘ Sum.inl = a.val .rv := by
    let x := unpackOriginalLift O hO power S U a
    have old := (liftBlowupCoordinatesWithRelativeFocus_apply O j U.label
      focus focusNonzero focusLabel x.1 x.2).1
    exact (congrArg Subtype.val old).trans (ObjectLift.tag_val U a)
  refine ⟨e,oldTag,?_⟩
  have inD (a) (ha : a ∈ ObjectLift.carrier U) :
      projectFields p (fieldTupleAssignment (a .vf)) ∈ D :=
    (projectFieldLift p (original (ObjectLift.tag U ⟨a,ha⟩) (a .vf)
      (fun i => by
        simpa only [Function.comp_apply,canonicalStructure_rvMap] using
          (congrFun (ObjectLift.tag_label U ⟨a,ha⟩) i).symm))).property
  apply (relative_blowup_graph_definable O hO power S p j F minusOne hm hF
    (ObjectLift.carrier U) (ObjectLift.definable U) D c inD cDef).congr
  intro a b
  suffices eq : ∀ ha : a ∈ ObjectLift.carrier U,
      (e ⟨a,ha⟩).val = updateBlowupPoint O j a
        (c ⟨projectFields p (fieldTupleAssignment (a .vf)),inD a ha⟩) by
    simp only [eq]
  intro ha
  let x := unpackOriginalLift O hO power S U ⟨a,ha⟩
  obtain ⟨_,mul,field⟩ := liftBlowupCoordinatesWithRelativeFocus_apply O j U.label
    focus focusNonzero focusLabel x.1 x.2
  funext s i
  cases s with
  | vf => exact congrFun field i
  | rv => cases i with
    | inl i => exact congrFun (oldTag ⟨a,ha⟩) i
    | inr i => cases i; exact mul

end GeneralizedEuler.Section5
