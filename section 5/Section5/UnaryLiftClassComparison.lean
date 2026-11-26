module

public import Section5.UnaryObjectLiftPresentation
import all Section5.UnaryTranslationClass
import all Section4.Objects
import all Section2.SortedStructure

/-! Recover the original degree-one RV class from the labels of its
unary lift. The active leading term is determined by the old RV tag. -/

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

local notation "𝓜" => canonicalStructure (L := L) O hO power

variable (U : RVObject (canonicalStructure (L := L) O hO power) S 1)

@[expose] def unaryLiftIndex : Fin (U.arity+1) ≃ Fin 1 ⊕ Fin U.arity :=
  finSumFinEquiv.symm.trans (Equiv.sumComm _ _)

theorem unaryLift_labelSet :
    reindexedUnaryLabels O (unaryLiftSet O hO power S U) (unaryLiftIndex O hO power S U) =
      appendUnaryLabelSet O U.carrier (fun r b => b = totalUnaryLabel O hO power S U r) := by
  classical
  ext w
  let t := w ∘ (unaryLiftIndex O hO power S U).symm
  let b := t (.inl 0)
  let r := t ∘ Sum.inr
  change t ∈ unaryLabelSet O (unaryLiftSet O hO power S U) ↔ r ∈ U.carrier ∧ b = totalUnaryLabel O hO power S U r
  rw [unaryLabelSet_iff_decoded O t]
  constructor
  · rintro ⟨x,⟨u,hu,hl⟩,same⟩
    have hr : u.val = r := hu.trans (congrArg (fun p : RV0 O × (Fin U.arity → RV0 O) => p.2) same)
    have htag : r ∈ U.carrier := hr ▸ u.property
    have eq : (⟨r,htag⟩ : U.carrier) = u := Subtype.ext hr.symm
    refine ⟨htag,?_⟩
    unfold totalUnaryLabel
    rw [dite_eq_left htag,eq]
    exact (congrArg (fun p : RV0 O × (Fin U.arity → RV0 O) => p.1) same).symm.trans hl.symm
  · rintro ⟨hr,h⟩
    unfold totalUnaryLabel at h
    rw [dite_eq_left hr] at h
    obtain ⟨x,hx⟩ := rv_surjective O b
    exact ⟨(x,r),⟨⟨r,hr⟩,rfl,h.symm.trans hx.symm⟩,Prod.ext hx rfl⟩

theorem unaryLift_labelClass :
    unaryLabelClass O hO power S (unaryLiftSet O hO power S U) (unaryLiftIndex O hO power S U)
      (unaryLiftSet_definable O hO power S U) (unaryLiftSet_pullback O hO power S U)
      (unaryLiftSet_finite O hO power S U) = objectClass 𝓜 S ⟨1,U⟩ := by
  classical
  let A := unaryLiftSet O hO power S U
  let idx := unaryLiftIndex O hO power S U
  let V := unaryLabelObjects O hO power S A idx (unaryLiftSet_definable O hO power S U)
    (unaryLiftSet_pullback O hO power S U) (unaryLiftSet_finite O hO power S U)
  have nz (w : Fin (U.arity+1) → RV0 O) (inLabels : w ∈ reindexedUnaryLabels O A idx) :
      w (idx.symm (.inl 0)) ≠ 0 := by
    have h : w ∈ reindexedUnaryLabels O (unaryLiftSet O hO power S U) (unaryLiftIndex O hO power S U) := inLabels
    rw [unaryLift_labelSet O hO power S U] at h
    let r := (w ∘ idx.symm) ∘ Sum.inr
    have hr : r ∈ U.carrier := h.1
    have eq : w (idx.symm (.inl 0)) = totalUnaryLabel O hO power S U r := h.2
    rw [eq,totalUnaryLabel,dite_eq_left hr]
    exact U.nonzero ⟨r,hr⟩ 0
  have empty : V.1.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro w h
    exact nz w h.1 h.2
  have pos : V.2.carrier = reindexedUnaryLabels O A idx := by
    ext w
    exact ⟨fun h => h.1,fun h => ⟨h,nz w h⟩⟩
  have zeroclass : objectClass 𝓜 S ⟨0,V.1⟩ = 0 := scissors_sound 𝓜 S (RVRelation.zero V.1 empty)
  change objectClass 𝓜 S ⟨0,V.1⟩ + objectClass 𝓜 S ⟨1,V.2⟩ = _
  rw [zeroclass,zero_add]
  apply scissors_sound 𝓜 S
  apply RVRelation.iso
  change RVDefinablyEquivalent 𝓜 S.carrier V.2.carrier U.carrier
  rw [pos.trans (unaryLift_labelSet O hO power S U)]
  exact (appendUnaryLabel_equiv O hO power S U.carrier U.definable _ (totalUnaryLabel_definable O hO power S U)).symm

variable (V : RVObject (canonicalStructure (L := L) O hO power) S 1)

@[expose] def unaryLiftBijection (f : ObjectLift.carrier U ≃ ObjectLift.carrier V) :
    unaryLiftSet O hO power S U ≃ unaryLiftSet O hO power S V :=
  (unaryLiftEquiv O hO power S U).symm.trans (f.trans (unaryLiftEquiv O hO power S V))

theorem unaryLiftBijection_definable (f : ObjectLift.carrier U ≃ ObjectLift.carrier V)
    (graph : DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ ObjectLift.carrier U, (f ⟨a,ha⟩).val = b)) :
    UnaryMixedGraphDefinable O hO power S (unaryLiftBijection O hO power S U V f) := by
  let e := unaryLiftEquiv O hO power S U
  let g := unaryLiftEquiv O hO power S V
  have eval (u : ObjectLift.carrier U) : (unaryLiftBijection O hO power S U V f (e u)).val = unaryPair O (f u).val := by
    change (g (f (e.symm (e u)))).val = _
    rw [e.symm_apply_apply]
    exact unaryLiftEquiv_apply O hO power S V (f u)
  refine graph.congr ?_
  intro a b
  constructor
  · rintro ⟨ha,eq⟩
    let u : ObjectLift.carrier U := ⟨a,ha⟩
    have hm : unaryPair O a ∈ unaryLiftSet O hO power S U := (mem_unaryLiftSet O hO power S U a).2 ha
    have he : (⟨unaryPair O a,hm⟩ : unaryLiftSet O hO power S U) = e u := Subtype.ext rfl
    refine ⟨hm,?_⟩
    change (unaryLiftBijection O hO power S U V f ⟨unaryPair O a,hm⟩).val = unaryPair O b
    rw [he,eval,eq]
  · rintro ⟨ha,eq⟩
    have hm : a ∈ ObjectLift.carrier U := (mem_unaryLiftSet O hO power S U a).1 ha
    let u : ObjectLift.carrier U := ⟨a,hm⟩
    have he : (⟨unaryPair O a,ha⟩ : unaryLiftSet O hO power S U) = e u := Subtype.ext rfl
    change (unaryLiftBijection O hO power S U V f ⟨unaryPair O a,ha⟩).val = unaryPair O b at eq
    rw [he,eval] at eq
    refine ⟨hm,?_⟩
    funext s i
    cases s
    · rw [Subsingleton.elim i (0 : Fin 1)]
      exact congrArg Prod.fst eq
    · exact congrFun (congrArg Prod.snd eq) i

theorem degree_one_lifts_have_common_blowup {H : Type} [Finite H]
    (f : ObjectLift.carrier U ≃ ObjectLift.carrier V)
    (graph : DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ ObjectLift.carrier U, (f ⟨a,ha⟩).val = b))
    (P : UnaryChartPartition O hO power S (unaryLiftBijection O hO power S U V f) H)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ H : Type, Finite H → RealizesFinitelySatisfiableTypes 𝓜 (CenterTestVariables S.carrier H)
      (CenterTestAssignments S.carrier H))
    (immediate : ∀ x y : K, (∀ c : S.carrier .vf, rv O (x-c.val) = rv O (y-c.val)) →
      ∃ a : SortedIsomorphism 𝓜 𝓜, a.toEmbedding .vf x = y ∧
        (∀ c ∈ S.carrier .vf, a.toEmbedding .vf c = c) ∧ ∀ t, a.toEmbedding .rv t = t)
    {eps : K} (he : eps ≠ 0) (small : O.valuation eps < 1)
    (hneg : rv O (-1) ∈ S.carrier .rv) :
    CommonBlowup (ElementaryClassStep O hO power S hneg) (objectClass 𝓜 S ⟨1,U⟩) (objectClass 𝓜 S ⟨1,V⟩) := by
  have common := unary_common_blowup_of_chart_partition O hO power S F minusOne hm hF sat immediate he small hneg
    (unaryLiftBijection O hO power S U V f) P (unaryLiftIndex O hO power S U) (unaryLiftIndex O hO power S V)
    (unaryLiftSet_definable O hO power S U) (unaryLiftSet_definable O hO power S V)
    (unaryLiftBijection_definable O hO power S U V f graph)
    (unaryLiftSet_pullback O hO power S U) (unaryLiftSet_pullback O hO power S V)
    (unaryLiftSet_finite O hO power S U) (unaryLiftSet_finite O hO power S V)
  simpa only [unaryLift_labelClass] using common

end GeneralizedEuler.Section5
