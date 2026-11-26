module

public import Section5.FiniteBaseLabels
public import Section5.RestoreCoordinates
public import Section5.ScaleTerms

/-! Finite RV bijections lift by diagonal scalings over the base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  {n : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable {U V : Set (labelAssignment n (CanonicalSort O))}

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem fieldExt {x y : fieldAssignment n (CanonicalSort O)} (h : x .vf = y .vf) :
    x = y := by
  funext s j
  cases s with
  | vf => exact congrFun h j
  | rv => exact j.elim

private theorem fieldLeadEq (x : fieldAssignment n (CanonicalSort O))
    (u : labelAssignment n (CanonicalSort O)) :
    fieldLead 𝓜 x = u ↔ ∀ j, rv O (x .vf j) = u .rv j := by
  constructor
  · intro h j
    simpa only [fieldLead, Function.comp_apply, canonicalStructure_rvMap] using
      congrFun (congrFun h .rv) j
  · intro h
    funext s j
    cases s with
    | vf => exact j.elim
    | rv => simpa only [fieldLead, Function.comp_apply, canonicalStructure_rvMap] using h j

private def fieldFiberEquiv (u : U) (a : Fin n → K) (hA : ∀ j, rv O (a j) = u.val .rv j) :
    ((liftedLabel (M := 𝓜) U) ⁻¹' {u} : Set (fieldLiftDomain 𝓜 U)) ≃
      {x : Fin n → K // ∀ j, rv O (x j) = rv O (a j)} where
  toFun x := ⟨x.val.val .vf,fun j =>
    (((fieldLeadEq (L := L) O hO power _ _).1 (congrArg Subtype.val x.property)) j).trans (hA j).symm⟩
  invFun x := by
    let y : fieldAssignment n (CanonicalSort O) := fieldTupleAssignment x.val
    have he := (fieldLeadEq (L := L) O hO power y u.val).2 (fun j => (x.property j).trans (hA j))
    let y' : fieldLiftDomain 𝓜 U := ⟨y, by change fieldLead 𝓜 y ∈ U; rw [he]; exact u.property⟩
    refine ⟨y',?_⟩
    change liftedLabel U y' = u
    exact Subtype.ext he
  left_inv x := Subtype.ext (Subtype.ext (fieldExt O rfl))
  right_inv x := rfl

/-- Combine the coordinatewise scalings of the individual polydiscs.
The same construction also works on arbitrary labels with representatives. -/
theorem liftByDiagonalScaling (e : U ≃ V)
    (a : U → Fin n → K) (b : V → Fin n → K)
    (ha : ∀ u j, rv O (a u j) = u.val .rv j)
    (hb : ∀ v j, rv O (b v j) = v.val .rv j)
    (aNZ : ∀ u j, a u j ≠ 0) (bNZ : ∀ v j, b v j ≠ 0) :
    ∃ lift : fieldLiftDomain 𝓜 U ≃ fieldLiftDomain 𝓜 V,
      (∀ x, liftedLabel V (lift x) = e (liftedLabel U x)) ∧
      ∀ x j, let u := liftedLabel (M := 𝓜) U x
        (lift x).val .vf j = b (e u) j * x.val .vf j / a u j := by
  let p := liftedLabel (M := 𝓜) U
  let q := liftedLabel (M := 𝓜) V
  let fiberEquiv (u : U) : (p ⁻¹' {u} : Set (fieldLiftDomain 𝓜 U)) ≃
      (q ⁻¹' {e u} : Set (fieldLiftDomain 𝓜 V)) :=
    (fieldFiberEquiv O hO power u (a u) (ha u)).trans
      ((scaleFibers O (a u) (b (e u)) (aNZ u) (bNZ (e u))).trans
        (fieldFiberEquiv O hO power (e u) (b (e u)) (hb (e u))).symm)
  let lift := (Equiv.sigmaPreimageEquiv p).symm.trans
    ((Equiv.sigmaCongr e fiberEquiv).trans (Equiv.sigmaPreimageEquiv q))
  refine ⟨lift,fun x => (fiberEquiv (p x) ⟨x,rfl⟩).property,?_⟩
  intro x j
  let u := p x
  let x' := fieldFiberEquiv O hO power u (a u) (ha u) ⟨x,rfl⟩
  change (scaleFibers O (a u) (b (e u)) (aNZ u) (bNZ (e u)) x').val j = _
  exact scaleFibers_apply O (a u) (b (e u)) (aNZ u) (bNZ (e u)) x' j

variable (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

private theorem basePolydisc_definable (a : Fin n → S.carrier .vf) :
    SortedDefinableOver 𝓜 S.carrier
      {x : fieldAssignment n (CanonicalSort O) | ∀ j, rv O (x .vf j) = rv O (a j).val} := by
  let t : labelAssignment n (CanonicalSort O) := rvTupleAssignment (fun j => rv O (a j).val)
  have ht (j : Fin n) : t .rv j ∈ S.carrier .rv := by
    simpa only [t, rvTupleAssignment, canonicalStructure_rvMap] using S.rvMap_mem (a j).property
  have h := definable_fieldLead_preimage (definable_base_label S t ht)
  convert h using 1
  ext x
  change (∀ j, rv O (x .vf j) = rv O (a j).val) ↔ fieldLead 𝓜 x = t
  exact (fieldLeadEq (L := L) O hO power x t).symm

/-- For a finite set of source labels the union of the diagonal graphs is
definable over the same base as the field representatives. -/
theorem definable_finite_label_lift (e : U ≃ V) [Finite U]
    (a : U → Fin n → S.carrier .vf) (b : V → Fin n → S.carrier .vf)
    (ha : ∀ u j, rv O (a u j).val = u.val .rv j)
    (hb : ∀ v j, rv O (b v j).val = v.val .rv j)
    (aNZ : ∀ u j, (a u j).val ≠ 0) (bNZ : ∀ v j, (b v j).val ≠ 0)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    HasDefinableFieldLift S e := by
  obtain ⟨lift,hLabel,hScale⟩ := liftByDiagonalScaling (L := L) O hO power e
    (fun u j => (a u j).val) (fun v j => (b v j).val) ha hb aNZ bNZ
  let T (u : U) : FieldTermTuple 𝓜 S (MixedVariables n Empty) n :=
    fun j => scaleVF F (.var (.inl (a u j))) (.var (.inl (b (e u) j))) (.var (.inr j))
  have hTerm (u : U) (x : fieldAssignment n (CanonicalSort O)) (j : Fin n) :
      realizeFieldTuple (T u) x .vf j = (b (e u) j).val * x .vf j / (a u j).val := by
    change (scaleVF F _ _ _).realize 𝓜 _ = _
    rw [eval_scaleVF O hO power F minusOne hm hF]
    rfl
  let D (u : U) : Set (fieldAssignment n (CanonicalSort O)) :=
    {x | ∀ j, rv O (x .vf j) = rv O (a u j).val}
  have hD (u : U) : SortedDefinableOver 𝓜 S.carrier (D u) :=
    basePolydisc_definable O hO power S (a u)
  have hDLabel (u : U) (x : fieldAssignment n (CanonicalSort O)) :
      x ∈ D u ↔ fieldLead 𝓜 x = u.val := by
    rw [fieldLeadEq (L := L) O hO power]
    simp only [D, Set.mem_ofPred_eq, ha]
  let W := MixedVariables n Empty
  let P (u : U) : Set (SortedAssignment (CanonicalSort O) (SumVariables W W)) :=
    {v | realizeFieldTuple (T u) (fun s => v s ∘ Sum.inl) = (fun s => v s ∘ Sum.inr) ∧
      (fun s => v s ∘ Sum.inl) ∈ D u}
  have hP (u : U) : SortedDefinableOver 𝓜 S.carrier (P u) :=
    (fieldTuple_graph (T u)).inter_left (hD u)
  refine ⟨lift,hLabel,?_⟩
  unfold DefinableRelation
  convert SortedDefinableOver.iUnion hP using 1
  ext v
  let x : fieldAssignment n (CanonicalSort O) := fun s => v s ∘ Sum.inl
  let y : fieldAssignment n (CanonicalSort O) := fun s => v s ∘ Sum.inr
  change (∃ hx : x ∈ fieldLiftDomain 𝓜 U, (lift ⟨x,hx⟩).val = y) ↔ v ∈ ⋃ u, P u
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨hx,hy⟩
    let u := liftedLabel (M := 𝓜) U ⟨x,hx⟩
    refine ⟨u,?_,(hDLabel u x).2 rfl⟩
    change realizeFieldTuple (T u) x = y
    rw [← hy]
    apply fieldExt O
    funext j
    exact (hTerm u x j).trans (hScale ⟨x,hx⟩ j).symm
  · rintro ⟨u,he,hx⟩
    have hLabel' := (hDLabel u x).1 hx
    have hx' : x ∈ fieldLiftDomain 𝓜 U := by
      change fieldLead 𝓜 x ∈ U
      rw [hLabel']
      exact u.property
    have hu : liftedLabel U ⟨x,hx'⟩ = u := Subtype.ext hLabel'
    refine ⟨hx',?_⟩
    change realizeFieldTuple (T u) x = y at he
    rw [← he]
    apply fieldExt O
    funext j
    exact (hScale ⟨x,hx'⟩ j).trans (by rw [hu,hTerm])

/-- Hypothesis 5.11 supplies both finite collections of field
representatives over the given base. -/
theorem definable_finite_label_lift_of_elementary (e : U ≃ V)
    (finiteU : U.Finite) (hU : SortedDefinableOver 𝓜 S.carrier U)
    (hV : SortedDefinableOver 𝓜 S.carrier V)
    (nonzeroU : ∀ u ∈ U, ∀ j, u .rv j ≠ 0) (nonzeroV : ∀ v ∈ V, ∀ j, v .rv j ≠ 0)
    (elem : ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → S.carrier s),
      φ.realize S.structureOn v ↔ φ.realize 𝓜 (fun s => Subtype.val ∘ v s))
    (generated : S.structureOn.IsVFGenerated)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    HasDefinableFieldLift S e := by
  let : Finite U := finiteU.to_subtype
  let hFin : Finite V := Finite.of_surjective e e.surjective
  have finiteV : V.Finite := Set.toFinite V
  obtain ⟨a,ha⟩ := finite_definable_labels_represented S elem generated U hU finiteU
  obtain ⟨b,hb⟩ := finite_definable_labels_represented S elem generated V hV finiteV
  simp only [canonicalStructure_rvMap] at ha hb
  have haNZ (u : U) (j : Fin n) : (a u j).val ≠ 0 :=
    fun he => nonzeroU u.val u.property j ((ha u j).symm.trans ((rv_eq_zero_iff O).2 he))
  have hbNZ (v : V) (j : Fin n) : (b v j).val ≠ 0 :=
    fun he => nonzeroV v.val v.property j ((hb v j).symm.trans ((rv_eq_zero_iff O).2 he))
  exact definable_finite_label_lift O hO power S e a b ha hb haNZ hbNZ F minusOne hm hF

end GeneralizedEuler.Section5
