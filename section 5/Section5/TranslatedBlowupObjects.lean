module

public import Section5.TranslatedBlowupLabels
public import Section5.BlowupClassProducts
import all Section4.Objects

/-! The positive labels after a focus translation carry the original
degree. Their structure map uses the new leading term itself. -/

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
  {k m : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1))
  (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (j : Fin (k+1))

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem translatedPositiveCarrier_definable (hneg : rv O (-1) ∈ S.carrier .rv) :
    isRVSet 𝓜 S (translatedPositiveCarrier O hO power S U idx j) := by
  let e := translatedPositiveEquiv O hO power S U idx j
  have he : SortedDefinableOver 𝓜 S.carrier (rvGraph (fun x => (e x).val)) :=
    translatedPositiveEquiv_definable O hO power S U idx j hneg
  have ran := definable_range_of_rvGraph (M := 𝓜) (A := S.carrier) (fun x => (e x).val) he
  have eq : Set.range (fun x => (e x).val) = translatedPositiveCarrier O hO power S U idx j := by
    ext y
    exact ⟨fun ⟨x,eX⟩ => eX ▸ (e x).property,
      fun hy => ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩⟩
  exact eq ▸ ran

@[expose] def translatedPositiveLabel (y : translatedPositiveCarrier O hO power S U idx j) :
    Fin (k+1) → RV0 O :=
  Function.update (U.label y.property.choose) j (y.val (blowupExtraIndex idx))

theorem translatedPositiveLabel_transport (x : positiveBlowupCarrier O hO power S U idx) :
    translatedPositiveLabel O hO power S U idx j (translatedPositiveEquiv O hO power S U idx j x) =
      positiveBlowupLabel O hO power S U idx j x := by
  let y := translatedPositiveEquiv O hO power S U idx j x
  let a : U.carrier := ⟨x.val ∘ blowupOldIndices idx,x.property.1⟩
  have h := translatedPositiveEquiv_apply O hO power S U idx j x
  have he : y.property.choose = a := Subtype.ext (y.property.choose_spec.1.trans h.1)
  change Function.update (U.label y.property.choose) j (y.val (blowupExtraIndex idx)) =
    Function.update (U.label a) j (x.val (blowupExtraIndex idx) * U.label a j)
  rw [he,h.2]

theorem translatedPositiveLabel_definable (hneg : rv O (-1) ∈ S.carrier .rv) :
    SortedDefinableOver 𝓜 S.carrier (rvGraph (translatedPositiveLabel O hO power S U idx j)) := by
  let e := translatedPositiveEquiv O hO power S U idx j
  have he : SortedDefinableOver 𝓜 S.carrier (rvGraph (fun x => (e x).val)) :=
    translatedPositiveEquiv_definable O hO power S U idx j hneg
  have hInv := definable_rvGraph_inverse (M := 𝓜) (A := S.carrier) e he
  have g := ObjectLift.relation_of_rvGraph (positiveBlowupLabel_definable O hO power S U idx hneg j)
  have comp := (ObjectLift.relation_of_rvGraph hInv).comp g
  apply rvGraph_of_relation (comp.congr ?_)
  intro a b
  constructor
  · rintro ⟨t,⟨y,hy,ht⟩,x,hx,hb⟩
    have eq : e.symm y = x := Subtype.ext (ht.trans hx.symm)
    have h := translatedPositiveLabel_transport O hO power S U idx j (e.symm y)
    change translatedPositiveLabel O hO power S U idx j (e (e.symm y)) = _ at h
    rw [e.apply_symm_apply,eq] at h
    exact ⟨y,hy,h.trans hb⟩
  · rintro ⟨y,hy,hb⟩
    let x := e.symm y
    have h := translatedPositiveLabel_transport O hO power S U idx j x
    change translatedPositiveLabel O hO power S U idx j (e (e.symm y)) = _ at h
    rw [e.apply_symm_apply] at h
    exact ⟨rvTupleAssignment x.val,⟨y,hy,rfl⟩,x,rfl,h.symm.trans hb⟩

@[expose] def translatedPositiveObject (hneg : rv O (-1) ∈ S.carrier .rv)
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    RVObject 𝓜 S (k+1) where
  arity := m
  carrier := translatedPositiveCarrier O hO power S U idx j
  definable := translatedPositiveCarrier_definable O hO power S U idx j hneg
  label := translatedPositiveLabel O hO power S U idx j
  graph := translatedPositiveLabel_definable O hO power S U idx j hneg
  nonzero := by
    intro y i
    obtain ⟨x,rfl⟩ := (translatedPositiveEquiv O hO power S U idx j).surjective y
    rw [translatedPositiveLabel_transport]
    exact (positiveBlowupObject O hO power S U idx hneg j finiteDelete).nonzero x i
  finiteFibers t := by
    let V := positiveBlowupObject O hO power S U idx hneg j finiteDelete
    let e := translatedPositiveEquiv O hO power S U idx j
    apply (V.finiteFibers t).of_injOn (f := e.symm) _ e.symm.injective.injOn
    intro y h
    have hEq := translatedPositiveLabel_transport O hO power S U idx j (e.symm y)
    change translatedPositiveLabel O hO power S U idx j (e (e.symm y)) = V.label (e.symm y) at hEq
    rw [e.apply_symm_apply] at hEq
    change V.label (e.symm y) = t
    exact hEq.symm.trans h

theorem translatedPositiveObject_class (hneg : rv O (-1) ∈ S.carrier .rv)
    (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite) :
    objectClass 𝓜 S ⟨k+1,translatedPositiveObject O hO power S U idx j hneg finiteDelete⟩ =
      objectClass 𝓜 S ⟨k+1,positiveBlowupObject O hO power S U idx hneg j finiteDelete⟩ := by
  symm
  apply scissors_sound 𝓜 S
  exact RVRelation.iso _ _ ⟨translatedPositiveEquiv O hO power S U idx j,
    translatedPositiveEquiv_definable O hO power S U idx j hneg⟩

end GeneralizedEuler.Section5
