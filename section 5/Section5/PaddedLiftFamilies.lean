module

public import Section5.PaddedFieldLift
public import Section5.PullbackHeadContractions

/-! A padded lift is a pullback family with its original RV tags
and with empty head start. -/

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

@[expose] def paddedLiftFamily : RetainedFieldFamily 𝓜 S n 0 where
  tags := Fin U.arity
  finiteTags := inferInstance
  select := Fin.elim0
  carrier := {q | (∃ u : U.carrier, u.val = q.2 ∧ U.label u = rv O ∘ q.1 ∘ p) ∧
    ∀ i ∉ Set.range p, q.1 i = 0}
  definable := by
    convert paddedLiftCarrier_definable O hO power S U p (Equiv.refl _) using 1
    ext a
    change ((_ ∧ _) : Prop) ↔
      (∃ u : U.carrier, u.val = a .rv ∧ U.label u = (𝓜).rvMap ∘ a .vf ∘ p) ∧
      (∀ i ∉ Set.range p, a .vf i = 0)
    have mapRV : (𝓜).rvMap = rv O := funext (canonicalStructure_rvMap O hO power)
    rw [mapRV,mixedTuple]
  finiteFibers x v := by
    have f := (U.finiteFibers (rv O ∘ x ∘ p)).image Subtype.val
    apply f.subset
    rintro _ ⟨⟨⟨u,rfl,e⟩,_⟩,_⟩
    exact ⟨u,e,rfl⟩

theorem paddedLiftFamily_pullback : (paddedLiftFamily O hO power S U p).IsFieldPullback O hO power S := by
  intro x y t h
  change ((∃ u : U.carrier, u.val = t ∧ U.label u = rv O ∘ x ∘ p) ∧ ∀ i ∉ Set.range p, x i = 0) ↔
    ((∃ u : U.carrier, u.val = t ∧ U.label u = rv O ∘ y ∘ p) ∧ ∀ i ∉ Set.range p, y i = 0)
  refine and_congr ?_ ?_
  · rw [show rv O ∘ x ∘ p = rv O ∘ y ∘ p from congrArg (· ∘ p) h]
  · apply forall_congr'
    intro i
    exact imp_congr_right (fun _ => ((rv_eq_zero_iff O).symm.trans
      ((congrArg (· = 0) (congrFun h i)).to_iff)).trans (rv_eq_zero_iff O))

end GeneralizedEuler.Section5
