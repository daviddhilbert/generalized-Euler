module

public import Section5.PaddedLiftFamilies
public import Section5.UnaryGradedClassComparison

/-! Recording the structure coordinates of an RV object and inserting
zeros gives a definable graph isomorphic to its original carrier. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {d n : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S d) (p : Fin d ↪ Fin n)

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def paddedRVLabels : Set (Fin n ⊕ Fin U.arity → RV0 O) :=
  {q | ∃ u : U.carrier, u.val = q ∘ Sum.inr ∧ U.label u = q ∘ Sum.inl ∘ p ∧
    ∀ i ∉ Set.range p, q (.inl i) = 0}

theorem paddedRVLabels_equivalent :
    RVDefinablyEquivalent 𝓜 S.carrier U.carrier (paddedRVLabels O hO power S U p) := by
  classical
  let B := paddedRVLabels O hO power S U p
  let values (u : U.carrier) : Fin n ⊕ Fin U.arity → RV0 O :=
    Sum.elim (Function.extend p (U.label u) (fun _ => 0)) u.val
  have eqn (u : U.carrier) : U.label u = values u ∘ Sum.inl ∘ p :=
    (Function.extend_comp p.injective (U.label u) (fun _ => 0)).symm
  have zeros (u : U.carrier) (i : Fin n) (hi : i ∉ Set.range p) : values u (.inl i) = 0 :=
    Function.extend_apply' (U.label u) (fun _ => (0 : RV0 O)) i hi
  let f (u : U.carrier) : B := ⟨values u,u,rfl,eqn u,zeros u⟩
  have inverse (u : U.carrier) (v : Fin n ⊕ Fin U.arity → RV0 O)
      (ht : u.val = v ∘ Sum.inr) (hl : U.label u = v ∘ Sum.inl ∘ p)
      (hz : ∀ i ∉ Set.range p, v (.inl i) = 0) : values u = v := by
    funext i
    rcases i with i | i
    · by_cases hi : i ∈ Set.range p
      · obtain ⟨j,rfl⟩ := hi
        exact (congrFun (eqn u) j).symm.trans (congrFun hl j)
      · exact (zeros u i hi).trans (hz i hi).symm
    · exact congrFun ht i
  have bij : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (congrArg (fun u : B => u.val ∘ Sum.inr) h)
    · intro q
      obtain ⟨u,ht,hl,hz⟩ := q.property
      exact ⟨u,Subtype.ext (inverse u q.val ht hl hz)⟩
  let e := Equiv.ofBijective f bij
  refine ⟨e,?_⟩
  let V := RVVariables (Fin U.arity ⊕ (Fin n ⊕ Fin U.arity))
  let ren : (s : TCsort) → RVVariables (Fin U.arity ⊕ Fin d) s → V s
    | .vf => PEmpty.elim
    | .rv => Sum.elim Sum.inl (Sum.inr ∘ Sum.inl ∘ p)
  have tags := SortedDefinableOver.iInter (fun i : Fin U.arity =>
    SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := V) .rv
      (.inl i) (.inr (.inr i)))
  have pad := SortedDefinableOver.iInter (fun i : {i : Fin n // i ∉ Set.range p} =>
    SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := V) .rv
      (.inr (.inl i.val)) rvZeroTerm)
  convert (U.graph.pullback_relabel ren).inter (tags.inter pad) using 1
  ext a
  let l := a .rv ∘ Sum.inl
  let r := a .rv ∘ Sum.inr
  have ev : (rvZeroTerm : SortedTerm L E (WithBase S.carrier V) .rv).realize 𝓜
      (fun s => Sum.elim Subtype.val (a s)) = 0 := realize_rvZeroTerm O hO power _
  simp only [rvGraph,Set.mem_inter_iff,Set.mem_iInter,Subtype.forall]
  change (∃ u : U.carrier, u.val = l ∧ values u = r) ↔
    (∃ u : U.carrier, u.val = l ∧ U.label u = r ∘ Sum.inl ∘ p) ∧
      (∀ i, l i = r (.inr i)) ∧ (∀ i ∉ Set.range p, r (.inl i) =
        (rvZeroTerm : SortedTerm L E (WithBase S.carrier V) .rv).realize 𝓜 (fun s => Sum.elim Subtype.val (a s)))
  simp only [ev]
  constructor
  · rintro ⟨u,hl,hr⟩
    exact ⟨⟨u,hl,hr ▸ eqn u⟩,fun i => (congrFun hl i).symm.trans (congrFun hr (.inr i)),
      hr ▸ zeros u⟩
  · rintro ⟨⟨u,hl,hq⟩,ht,hz⟩
    exact ⟨u,hl,inverse u r (hl.trans (funext ht)) hq hz⟩

end GeneralizedEuler.Section5
