module

public import Section5.BlowupMultiplierDefinability
public import Section5.GradedBlowupLabels
public import Section5.ZeroBlowupObject

/-! The positive-degree stratum, retaining the extra nonzero multiplier
as part of the RV carrier. -/

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
  {m k : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1))
  (idx : Fin m ≃ Fin U.arity ⊕ Fin 1)

private abbrev oldIndices := idx.symm ∘ Sum.inl
private abbrev extraIndex := idx.symm (Sum.inr 0)

/-- The old coordinates and the additional multiplier are both visible
in the underlying RV carrier. -/
@[expose] def positiveBlowupCarrier : Set (Fin m → RV0 O) :=
  {x | x ∘ idx.symm ∘ Sum.inl ∈ U.carrier ∧
    unsignedValue O (x (idx.symm (Sum.inr 0))) < 1 ∧ x (idx.symm (Sum.inr 0)) ≠ 0}

theorem positiveBlowupCarrier_definable (hneg : rv O (-1) ∈ S.carrier .rv) :
    isRVSet 𝓜 S (positiveBlowupCarrier O hO power S U idx) := by
  have defOld := isRVSet_precomp (oldIndices O hO power S U idx) U.definable
  have defNew := isRVSet_precomp (fun _ : Fin 1 => extraIndex O hO power S U idx)
    (nonzero_multipliers_definable O hO power S hneg)
  exact isRVSet_inter defOld defNew

@[expose] def positiveBlowupLabel (j : Fin (k+1))
    (x : positiveBlowupCarrier O hO power S U idx) : Fin (k+1) → RV0 O :=
  blowupLabel O j U.label (⟨x.val ∘ idx.symm ∘ Sum.inl,x.property.1⟩,x.val (idx.symm (Sum.inr 0)))

theorem positiveBlowupLabel_definable (hneg : rv O (-1) ∈ S.carrier .rv) (j : Fin (k+1)) :
    SortedDefinableOver 𝓜 S.carrier (rvGraph (positiveBlowupLabel O hO power S U idx j)) := by
  let X := RVVariables (Fin m ⊕ Fin (k+1))
  let Y := RVVariables (Fin (k+1))
  let W := SumVariables X Y
  let p := oldIndices O hO power S U idx
  let q := extraIndex O hO power S U idx
  let toOld : ∀ s, RVVariables (Fin U.arity ⊕ Fin (k+1)) s → W s
    | .vf => PEmpty.elim
    | .rv => Sum.elim (Sum.inl ∘ Sum.inl ∘ p) Sum.inr
  have oldGraph := U.graph.pullback_relabel toOld
  let T := WithBase S.carrier W
  let τ (i : Fin (k+1)) : SortedTerm L E T .rv :=
    if i = j then rvMulTerm (.var (.inr (.inl (.inl q)))) (.var (.inr (.inr i)))
    else .var (.inr (.inr i))
  have coordinate (i : Fin (k+1)) := SortedDefinableOver.coordinate_eq_term
    (M := 𝓜) (A := S.carrier) (Var := W) .rv (.inl (.inr i)) (τ i)
  have comparison : SortedDefinableOver 𝓜 S.carrier
      {w : SortedAssignment (CanonicalSort O) W | ∀ i : Fin (k+1),
        w .rv (.inl (.inr i)) =
          Function.update (w .rv ∘ Sum.inr) j (w .rv (.inl (.inl q)) * w .rv (.inr j)) i} := by
    convert SortedDefinableOver.iInter coordinate using 1
    ext w
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    apply forall_congr'
    intro i
    by_cases h : i = j
    · subst i
      simp only [τ, ite_true, Function.update_self, realize_rvMulTerm O hO power,
        SortedTerm.realize, Sum.elim_inr]
    · simp only [τ,ite_eq_right h,Function.update_of_ne h,SortedTerm.realize,Sum.elim_inr,Function.comp_apply]
  let toCarrier : ∀ s, RVVariables (Fin m) s → X s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  have own := (positiveBlowupCarrier_definable O hO power S U idx hneg).pullback_relabel toCarrier
  have hh := own.inter (definable_project_mixed (oldGraph.inter comparison))
  have eq : rvGraph (positiveBlowupLabel O hO power S U idx j) =
      {w : SortedAssignment (CanonicalSort O) X |
        (w .rv ∘ Sum.inl) ∈ positiveBlowupCarrier O hO power S U idx ∧
        ∃ a : labelAssignment (k+1) (CanonicalSort O),
          (∃ u : U.carrier, u.val = w .rv ∘ Sum.inl ∘ p ∧ U.label u = a .rv) ∧
          (∀ i : Fin (k+1), w .rv (.inr i) =
            Function.update (a .rv) j (w .rv (.inl q) * a .rv j) i)} := by
    ext w
    constructor
    · rintro ⟨x,hx,hOutput⟩
      have hm : w .rv ∘ Sum.inl ∈ positiveBlowupCarrier O hO power S U idx := hx ▸ x.property
      let a : U.carrier := ⟨w .rv ∘ Sum.inl ∘ p,hm.1⟩
      refine ⟨hm,rvTupleAssignment (U.label a),⟨a,rfl,rfl⟩,?_⟩
      intro i
      have hX : x = ⟨w .rv ∘ Sum.inl,hm⟩ := Subtype.ext hx
      exact (congrFun ((congrArg (positiveBlowupLabel O hO power S U idx j) hX).symm.trans hOutput) i).symm
    · rintro ⟨hm,a,⟨u,hu,ha⟩,hs⟩
      let x : positiveBlowupCarrier O hO power S U idx := ⟨w .rv ∘ Sum.inl,hm⟩
      have hU : u = (⟨x.val ∘ idx.symm ∘ Sum.inl,x.property.1⟩ : U.carrier) :=
        Subtype.ext hu
      have hA : a .rv = U.label ⟨x.val ∘ idx.symm ∘ Sum.inl,x.property.1⟩ :=
        ha.symm.trans (congrArg U.label hU)
      refine ⟨x,rfl,?_⟩
      funext i
      have he := (hs i).symm
      rw [hA] at he
      exact he
  rw [eq]
  exact hh

/-- The original degree survives on the nonzero-multiplier stratum.
The finite fibers follow from the deleted-label bound and recovery of
the multiplier from the changed coordinate. -/
@[expose] def positiveBlowupObject (hneg : rv O (-1) ∈ S.carrier .rv) (j : Fin (k+1))
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    RVObject 𝓜 S (k+1) where
  arity := m
  carrier := positiveBlowupCarrier O hO power S U idx
  definable := positiveBlowupCarrier_definable O hO power S U idx hneg
  label := positiveBlowupLabel O hO power S U idx j
  graph := positiveBlowupLabel_definable O hO power S U idx hneg j
  nonzero x i := blowupLabel_nonzero O j U.label _ (U.nonzero _) x.property.2.2 i
  finiteFibers t := by
    let Z := zeroBlowupObject U j finiteDelete
    have small (r : {i : Fin (k+1) // i ≠ j} → RV0 O) :
        ((deleteCoordinate j ∘ U.label) ⁻¹' {r}).Finite := by
      let v : Fin k → RV0 O := fun i => r ⟨j.succAbove i,Fin.succAbove_ne _ _⟩
      apply (Z.finiteFibers v).subset
      intro x hx
      change U.label x ∘ j.succAbove = v
      funext i
      exact congrFun (show deleteCoordinate j (U.label x) = r from hx) ⟨j.succAbove i,Fin.succAbove_ne _ _⟩
    let forget (x : positiveBlowupCarrier O hO power S U idx) : U.carrier × RV0 O :=
      (⟨x.val ∘ idx.symm ∘ Sum.inl,x.property.1⟩,x.val (idx.symm (Sum.inr 0)))
    have inj : Function.Injective forget := by
      intro x y he
      apply Subtype.ext
      funext i
      obtain ⟨c,rfl⟩ := idx.symm.surjective i
      cases c with
      | inl j => exact congrFun (congrArg (fun a => a.1.val) he) j
      | inr j =>
        have h : j = 0 := Subsingleton.elim _ _
        subst j
        exact congrArg Prod.snd he
    have finiteT := blowup_finite_fibers O j U.label (fun x => U.nonzero x j) small t
    change (forget ⁻¹' (blowupLabel O j U.label ⁻¹' {t})).Finite
    exact finiteT.preimage inj.injOn

end GeneralizedEuler.Section5
