module

public import Section5.RelativeRVRows
public import Section5.UnaryGradedClassComparison
public import Section5.ObjectLiftRestrictions

/-! Restrict a relative row to a definable locus and glue the cut.
The rest of the carrier has its old active label. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {h t k : ℕ} {I : RelativeRVIndex M S h t}

namespace RelativeRVRow

variable (A : RelativeRVRow I k)

abbrev LocusVars (A : RelativeRVRow I k) :=
  SumVariables (RVVariables (Fin h)) (RVVariables (Fin A.arity))

@[expose] def restrictRow (C : Set (SortedAssignment X A.LocusVars))
    (defC : SortedDefinableOver M S.carrier C) : RelativeRVRow I k where
  arity := A.arity
  tags := A.tags ∩ C
  tagsDefinable := A.tagsDefinable.inter defC
  graph := A.graph ∩ {a | (fun s => a s ∘ Sum.inl) ∈ C}
  graphDefinable := A.graphDefinable.inter (defC.pullback_relabel (fun _ => Sum.inl))
  valid := by
    intro p hp
    obtain ⟨b,valid⟩ := A.valid p hp
    refine ⟨b,?_,?_,?_,?_⟩
    · intro u
      change (appendAssignments (rvTupleAssignment p) u ∈ A.tags ∧ appendAssignments (rvTupleAssignment p) u ∈ C) ↔
        ∃ v, appendAssignments (appendAssignments (rvTupleAssignment p) u) v ∈ A.graph ∧
          appendAssignments (rvTupleAssignment p) u ∈ C
      rw [valid.1 u]
      constructor
      · rintro ⟨⟨v,h⟩,c⟩
        exact ⟨v,h,c⟩
      · rintro ⟨v,h,c⟩
        exact ⟨⟨v,h⟩,c⟩
    · exact fun u v w hv hw => valid.2.1 u v w hv.1 hw.1
    · exact fun u v hv => valid.2.2.1 u v hv.1
    · exact fun v f hf => valid.2.2.2 v f (fun i => (hf i).1)

theorem gluedClass_cut (C : Set (SortedAssignment X A.LocusVars))
    (defC : SortedDefinableOver M S.carrier C) :
    A.gluedClass = (A.restrictRow C defC).gluedClass + (A.restrictRow Cᶜ defC.compl).gluedClass := by
  classical
  let B := A.restrictRow C defC
  let D := A.restrictRow Cᶜ defC.compl
  let W := A.object
  let Q := gluedRVTags I.labels C
  obtain ⟨e,he⟩ := A.object_carrier_equiv
  let mark := {x | ∃ hx : x ∈ W.carrier, (e ⟨x,hx⟩).val ∈ Q}
  have defMark : isRVSet M S mark := by
    have pre := (ObjectLift.relation_of_rvGraph he).preimage (gluedRVTags_definable I.definable defC)
    unfold isRVSet
    convert pre using 1
    ext x
    constructor
    · rintro ⟨hx,hQ⟩
      exact ⟨rvTupleAssignment (e ⟨x .rv,hx⟩).val,hQ,⟨x .rv,hx⟩,rfl,rfl⟩
    · rintro ⟨y,hy,a,eq,ey⟩
      have ha : x .rv ∈ W.carrier := eq ▸ a.property
      have e : (⟨x .rv,ha⟩ : W.carrier) = a := Subtype.ext eq.symm
      exact ⟨ha,e.symm ▸ ey.symm ▸ hy⟩
  let U₁ := {x ∈ W.carrier | x ∈ mark}
  let U₂ := {x ∈ W.carrier | x ∉ mark}
  have def₁ : isRVSet M S U₁ := W.definable.inter defMark
  have def₂ : isRVSet M S U₂ := W.definable.inter defMark.compl
  have disj : Disjoint U₁ U₂ :=
    Set.disjoint_left.2 (fun _ hu hv => hv.2 hu.2)
  have cover : U₁ ∪ U₂ = W.carrier := by
    ext x
    exact ⟨fun h => h.elim And.left And.left,fun h =>
      if p : x ∈ mark then Or.inl ⟨h,p⟩ else Or.inr ⟨h,p⟩⟩
  have preserved (x : W.carrier) : x.val ∈ mark ↔ (e x).val ∈ Q :=
    ⟨fun ⟨_,h⟩ => h,fun h => ⟨x.property,h⟩⟩
  have hB := rvDefinableEquiv_of_preserved_cut (S := S) e he (· ∈ mark) (· ∈ Q) preserved def₁
  have hD := rvDefinableEquiv_of_preserved_cut (S := S) e he (· ∉ mark) (· ∉ Q)
    (fun x => not_congr (preserved x)) def₂
  have eB : {x ∈ gluedRVTags I.labels A.tags | x ∈ Q} = gluedRVTags I.labels B.tags := by
    ext x
    constructor
    · rintro ⟨⟨p,h⟩,⟨_,c⟩⟩
      exact ⟨p,h,c⟩
    · rintro ⟨p,h,c⟩
      exact ⟨⟨p,h⟩,p,c⟩
  have eD : {x ∈ gluedRVTags I.labels A.tags | x ∉ Q} = gluedRVTags I.labels D.tags := by
    ext x
    constructor
    · rintro ⟨⟨p,h⟩,hc⟩
      exact ⟨p,h,fun c => hc ⟨p,c⟩⟩
    · rintro ⟨p,h,c⟩
      exact ⟨⟨p,h⟩,fun hQ => c hQ.2⟩
  rw [eB] at hB
  rw [eD] at hD
  change objectClass M S ⟨_,W⟩ = objectClass M S ⟨_,B.object⟩ + objectClass M S ⟨_,D.object⟩
  unfold objectClass
  rw [← map_add]
  exact scissors_sound M S (.cut _ _ _ U₁ U₂ def₁ def₂ disj cover
    (hB.trans B.object_carrier_equiv.symm) (hD.trans D.object_carrier_equiv.symm))

end RelativeRVRow

end GeneralizedEuler.Section5
