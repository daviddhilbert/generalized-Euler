module

public import Section5.PreparedMapOperations
public import Section2.RVMonomials

/-! Definable tests indexed by an external RV tuple. A Boolean code
combines a domain test with the output tests without enlarging the
physical input of a preparation. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M}
  {n m : ℕ} {I J R : Type}

abbrev PointTests (O : ValuationSubring K) (n : ℕ) (I J : Type) :=
  Set (PreparationPoint O (Fin n) I × (J → RV0 O))

@[expose] def PointTestsDefinable
    (M : SortedStructure L E (CanonicalSort O)) (S : SortedSubstructure M)
    (G : PointTests O n I J) : Prop :=
  DefinableRelation M S.carrier
    (fun a : SortedAssignment (CanonicalSort O) (MixedVariables n I) =>
      fun b : SortedAssignment (CanonicalSort O) (RVVariables J) =>
        (mixedTuple a, b .rv) ∈ G)

namespace PointTestsDefinable

theorem transport [Finite I]
    {f : PreparationPoint O (Fin n) I → PreparationPoint O (Fin m) R}
    {G : PointTests O n I J}
    (hf : PointMapDefinable M S f) (hG : PointTestsDefinable M S G) :
    PointTestsDefinable M S {q | ∃ p, f p = q.1 ∧ (p,q.2) ∈ G} := by
  unfold PointMapDefinable at hf
  unfold PointTestsDefinable at hG ⊢
  exact (hf.transport hG).congr fun y t => by
    constructor
    · rintro ⟨a, ha, ht⟩
      exact ⟨mixedTuple a, ha, ht⟩
    · rintro ⟨p, hp, ht⟩
      obtain ⟨a, rfl⟩ := mixedTuple_surjective p
      exact ⟨a, hp, ht⟩

theorem univ : PointTestsDefinable M S (Set.univ : PointTests O n I J) := by
  unfold PointTestsDefinable DefinableRelation
  refine ⟨SortedFormula.falsum.neg, fun x => ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩⟩
  rw [SortedFormula.realize_neg]
  exact id

end PointTestsDefinable

/-- The zero tag selects the ambient test. All other tag values select
the graph test and keep exactly its original output indices. -/
@[expose] def flagTests (A G : PointTests O n I J) : PointTests O n I (Option J) :=
  {p | (p.2 none = 0 ∧ (p.1, p.2 ∘ some) ∈ A) ∨
    (p.2 none ≠ 0 ∧ (p.1, p.2 ∘ some) ∈ G)}

section Flags

variable [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K] [L.Structure (Residue O)]
  (hc : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (B : SortedSubstructure (canonicalStructure (L := L) O hc power))

local notation "𝓜" => canonicalStructure (L := L) O hc power

theorem flagTests_definable {A G : PointTests O n I J}
    (hA : PointTestsDefinable 𝓜 B A) (hG : PointTestsDefinable 𝓜 B G) :
    PointTestsDefinable 𝓜 B (flagTests A G) := by
  let V := SumVariables (MixedVariables n I) (RVVariables (Option J))
  let rename : ∀ s, SumVariables (MixedVariables n I) (RVVariables J) s → V s
    | .vf => id
    | .rv => Sum.map id some
  have hz : SortedDefinableOver 𝓜 B.carrier
      {a : SortedAssignment (CanonicalSort O) V | a .rv (.inr none) = 0} := by
    have hz' := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := B.carrier) (Var := V)
      .rv (.inr none) rvZeroTerm
    simpa only [realize_rvZeroTerm O hc power] using hz'
  unfold PointTestsDefinable DefinableRelation at hA hG ⊢
  exact (hz.inter (hA.pullback_relabel rename)).union (hz.compl.inter (hG.pullback_relabel rename))

end Flags

end GeneralizedEuler.Section5
