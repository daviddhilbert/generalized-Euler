module

public import Section5.PairedUnaryGraphs
import all Section5.UnaryCenterChains

/-! The chosen focus for a center test has a fixed-base graph when the
center depends definably on the retained RV tag. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {J : Type} [Finite J] {B : Set (K × (J → RV0 O))}

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem centerFocus_graph_definable
    (c : (J → RV0 O) → K) (a : B)
    (hB : SortedDefinableOver 𝓜 S.carrier
      {y : SortedAssignment (CanonicalSort O) (MixedVariables 1 J) | unaryPair O y ∈ B})
    (hc : DefinableRelation 𝓜 S.carrier (fun
      (r : SortedAssignment (CanonicalSort O) (RVVariables J))
      (v : fieldAssignment 1 (CanonicalSort O)) => c (r .rv) = v .vf 0)) :
    targetFocusGraphDefinable O hO power S (centerLocus (A := B) O c) (centerFocus O c a) := by
  let W := MixedVariables 1 J
  let rename : ∀ s, SumVariables (RVVariables J) (MixedVariables 1 Empty) s → W s
    | .vf => Sum.elim PEmpty.elim id
    | .rv => Sum.elim id Empty.elim
  unfold DefinableRelation at hc
  have eq := hc.pullback_relabel rename
  have nonzero := (field_eq_zero_definable O hO power S (V := W) 0).compl
  have selected : SortedDefinableOver 𝓜 S.carrier
      {y : SortedAssignment (CanonicalSort O) W | unaryPair O y ∈ B ∧ c (y .rv) = y .vf 0 ∧ y .vf 0 ≠ 0} :=
    hB.inter (eq.inter nonzero)
  have graph := ((unaryLabelAssignment_definable O hO power S (H := J)).inter_left selected).transpose
  refine graph.congr ?_
  intro t y
  let d := decodeUnaryLabel O (t .rv)
  constructor
  · rintro ⟨label,hy,hc',hn⟩
    have he : unaryMixedLabel O (unaryPair O y) = d :=
      congrArg (fun w : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1 ⊕ J)) =>
        decodeUnaryLabel O (w .rv)) label
    have tag : y .rv = d.2 := congrArg Prod.snd he
    have lead : rv O (y .vf 0) = d.1 := congrArg Prod.fst he
    have focus : (c d.2,d.2) = unaryPair O y := Prod.ext ((congrArg c tag).symm.trans hc') tag.symm
    have loc : d ∈ centerLocus (A := B) O c := ⟨focus.symm ▸ hy,
      lead ▸ (rv_eq_zero_iff O).not.2 hn,by rw [← tag,hc',lead]⟩
    refine ⟨loc,?_⟩
    change (centerFocus O c a d).val = unaryPair O y
    unfold centerFocus
    rw [dite_eq_left loc]
    exact focus
  · rintro ⟨loc,h⟩
    change (centerFocus O c a d).val = unaryPair O y at h
    unfold centerFocus at h
    rw [dite_eq_left loc] at h
    have tag : d.2 = y .rv := congrArg Prod.snd h
    have field : c d.2 = y .vf 0 := congrArg Prod.fst h
    have lead : rv O (y .vf 0) = d.1 := by rw [← field]; exact loc.2.2
    refine ⟨?_,h ▸ loc.1,(congrArg c tag.symm).trans field,?_⟩
    · funext s i
      cases s with
      | vf => exact i.elim
      | rv =>
        cases i with
        | inl i =>
          rw [Subsingleton.elim i (0 : Fin 1)]
          exact lead
        | inr i => exact (congrFun tag i).symm
    · intro hz
      rw [hz,map_zero] at lead
      exact loc.2.1 lead.symm

end GeneralizedEuler.Section5
