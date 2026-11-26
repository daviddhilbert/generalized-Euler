module

public import Section5.LiftClassHom
public import Section2.RVMonomials

/-! Pad the unused field coordinates by zero and reindex the old RV
tags. This does not change the VF class of a lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {n d m : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S d)
  (p : Fin d ↪ Fin n) (r : Fin m ≃ Fin U.arity)

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def paddedLiftProjection :
    SortedAssignment (CanonicalSort O) (MixedVariables n (Fin m)) →
      SortedAssignment (CanonicalSort O) (ObjectLift.Vars U) :=
  fun x s => match s with
    | .vf => x .vf ∘ p
    | .rv => x .rv ∘ r.symm

@[expose] def paddedLiftCarrier :
    Set (SortedAssignment (CanonicalSort O) (MixedVariables n (Fin m))) :=
  {x | paddedLiftProjection O hO power S U p r x ∈ ObjectLift.carrier U ∧
    ∀ i ∉ Set.range p, x .vf i = 0}

theorem field_eq_zero_definable {V : TCsort → Type} (i : V .vf) :
    SortedDefinableOver 𝓜 S.carrier {x : SortedAssignment (CanonicalSort O) V | x .vf i = 0} := by
  refine ⟨SortedFormula.equal (rvOfVF (.var (.inr i))) rvZeroTerm,fun x => ?_⟩
  rw [SortedFormula.realize]
  rw [eval_rvOfVF O hO power,realize_rvZeroTerm O hO power]
  exact (rv_eq_zero_iff O).symm

theorem paddedLiftCarrier_definable :
    SortedDefinableOver 𝓜 S.carrier (paddedLiftCarrier O hO power S U p r) := by
  let rename : ∀ s, ObjectLift.Vars U s → MixedVariables n (Fin m) s
    | .vf => p
    | .rv => r.symm
  have defProj := (ObjectLift.definable U).pullback_relabel rename
  have defZero := SortedDefinableOver.iInter (fun i : {i : Fin n // i ∉ Set.range p} =>
    field_eq_zero_definable O hO power S (V := MixedVariables n (Fin m)) i.val)
  convert defProj.inter defZero using 1
  ext x
  simp only [paddedLiftCarrier,Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq,Subtype.forall]
  rfl

theorem paddedLift_iso :
    MixedDefinablyEquivalent 𝓜 S (paddedLiftCarrier O hO power S U p r) (ObjectLift.carrier U) := by
  classical
  let Y := paddedLiftCarrier O hO power S U p r
  let f (x : Y) : ObjectLift.carrier U :=
    ⟨paddedLiftProjection O hO power S U p r x.val,x.property.1⟩
  have bij : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      funext s i
      cases s with
      | vf =>
        by_cases h : i ∈ Set.range p
        · obtain ⟨j,rfl⟩ := h
          exact congrFun (congrFun (congrArg Subtype.val he) .vf) j
        · exact (x.property.2 i h).trans (y.property.2 i h).symm
      | rv =>
        obtain ⟨j,rfl⟩ := r.symm.surjective i
        exact congrFun (congrFun (congrArg Subtype.val he) .rv) j
    · intro y
      let v : SortedAssignment (CanonicalSort O) (MixedVariables n (Fin m))
        | .vf => Function.extend p (y.val .vf) (fun _ => 0)
        | .rv => y.val .rv ∘ r
      have eq : paddedLiftProjection O hO power S U p r v = y.val := by
        funext s i
        cases s with
        | vf =>
          change Function.extend p (y.val .vf) (fun _ => 0) (p i) = y.val .vf i
          exact congrFun (Function.extend_comp p.injective (y.val .vf) (fun _ => 0)) i
        | rv => exact congrArg (y.val .rv) (r.apply_symm_apply i)
      have h : v ∈ Y := by
        refine ⟨eq.symm ▸ y.property,?_⟩
        intro i hi
        exact Function.extend_apply' _ _ _ hi
      exact ⟨⟨v,h⟩,Subtype.ext eq⟩
  refine ⟨Equiv.ofBijective f bij,?_⟩
  let V := MixedVariables n (Fin m)
  let W := ObjectLift.Vars U
  let T := SumVariables V W
  have source := (paddedLiftCarrier_definable O hO power S U p r).pullback_relabel
    (fun s => (Sum.inl : V s → T s))
  have hf := SortedDefinableOver.iInter (fun i : Fin d =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := T) .vf
      (.inl (p i)) (.inr i))
  have hr := SortedDefinableOver.iInter (fun i : Fin U.arity =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := T) .rv
      (.inl (r.symm i)) (.inr i))
  unfold DefinableRelation
  convert source.inter (hf.inter hr) using 1
  ext a
  let x : SortedAssignment (CanonicalSort O) V := fun s => a s ∘ Sum.inl
  let y : SortedAssignment (CanonicalSort O) W := fun s => a s ∘ Sum.inr
  simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
  change (∃ hx : x ∈ Y, paddedLiftProjection O hO power S U p r x = y) ↔
    x ∈ Y ∧ (∀ i : Fin d, x .vf (p i) = y .vf i) ∧ (∀ i : Fin U.arity, x .rv (r.symm i) = y .rv i)
  constructor
  · rintro ⟨hx,eq⟩
    exact ⟨hx,fun i => congrFun (congrFun eq .vf) i,fun i => congrFun (congrFun eq .rv) i⟩
  · rintro ⟨hx,hf,hr⟩
    refine ⟨hx,?_⟩
    funext s i
    cases s with
    | vf => exact hf i
    | rv => exact hr i

end GeneralizedEuler.Section5
