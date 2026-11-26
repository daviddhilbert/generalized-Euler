module

public import Section5.PaddedFieldLift
public import Section5.DefinableBijectionSchemes
public import Section3.DiscPartitionFormula

/-! The shape of a unary fiber is a first-order test. Disc centers
and radius representatives are quantified in the model. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty

theorem represented_openDisc_definable {V : TCsort → Type}
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (x c r : V .vf) :
    SortedDefinableOver 𝓜 S.carrier
      {p : SortedAssignment Z V | p .vf x ∈ openDisc O (p .vf c) (O.valuation (p .vf r))} := by
  let φ := discMemberFormula F false (.var (0 : Fin 3)) (.var 1) (.var 2)
  let q : Fin 3 → V .vf := ![x,c,r]
  refine ⟨liftValuedFormula minusOne φ (Sum.elim (fun i => .var (.inr (q i))) Fin.elim0),?_⟩
  intro p
  rw [realize_liftValuedFormula,recoveredValuedStructure_canonical_eq O hO power minusOne hm]
  let := convexStructure O L
  let v : Fin 3 → K := p .vf ∘ q
  have go (w : Fin 0 → K) : BoundedFormula.Realize φ v w ↔ v 0 ∈ openDisc O (v 1) (O.valuation (v 2)) := by
    rw [Subsingleton.elim w default]
    exact realize_discMemberFormula O hF false _ _ _ _
  exact (go _).symm

variable {P : TCsort → Type}

theorem unary_fiber_equal_definable
    {D G : Set (SortedAssignment Z (SumVariables P U))}
    (d : SortedDefinableOver 𝓜 S.carrier D) (g : SortedDefinableOver 𝓜 S.carrier G) :
    SortedDefinableOver 𝓜 S.carrier {p | ∀ a : fieldAssignment 1 Z,
      appendAssignments p a ∈ D ↔ appendAssignments p a ∈ G} := by
  have tests := definable_forall_assignments ((d.inter g).union (d.compl.inter g.compl))
  convert tests using 1
  ext p
  exact forall_congr' fun a =>
    ⟨fun h => by
      classical
      by_cases ha : appendAssignments p a ∈ D
      · exact Or.inl ⟨ha,h.1 ha⟩
      · exact Or.inr ⟨ha,ha ∘ h.2⟩,
      fun h => h.elim (fun yes => iff_of_true yes.1 yes.2) (fun no => iff_of_false no.1 no.2)⟩

theorem unary_openDisc_fiber_definable
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : Set (SortedAssignment Z (SumVariables P U)))
    (defD : SortedDefinableOver 𝓜 S.carrier D) :
    SortedDefinableOver 𝓜 S.carrier {p | ∃ (c : K) (r : O.ValueGroup), r ≠ 0 ∧
      ∀ a : fieldAssignment 1 Z, appendAssignments p a ∈ D ↔ a .vf 0 ∈ openDisc O c r} := by
  let V := MixedVariables 2 Empty
  let W := SumVariables P V
  let T := SumVariables W U
  let take (s : TCsort) : SumVariables P U s → T s := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have ball := represented_openDisc_definable O hO power S F minusOne hm hF (V := T)
    (.inr 0) (.inl (.inr 0)) (.inl (.inr 1))
  have agree := unary_fiber_equal_definable O hO power S (defD.pullback_relabel take) ball
  have radius := (field_eq_zero_definable O hO power S (V := W) (.inr 1)).compl
  convert definable_project_mixed (radius.inter agree) using 1
  ext p
  have relabel (v : SortedAssignment Z V) (a : fieldAssignment 1 Z) :
      (fun s => appendAssignments (appendAssignments p v) a s ∘ take s) = appendAssignments p a := by
    funext s i
    rcases i with i | i <;> rfl
  simp only [Set.mem_inter_iff,Set.mem_compl_iff]
  change (∃ (c : K) (r : O.ValueGroup), r ≠ 0 ∧
      ∀ a : fieldAssignment 1 Z, appendAssignments p a ∈ D ↔ a .vf 0 ∈ openDisc O c r) ↔
    ∃ v : SortedAssignment Z V, v .vf 1 ≠ 0 ∧
      ∀ a : fieldAssignment 1 Z, (fun s => appendAssignments (appendAssignments p v) a s ∘ take s) ∈ D ↔
        a .vf 0 ∈ openDisc O (v .vf 0) (O.valuation (v .vf 1))
  simp only [relabel]
  constructor
  · rintro ⟨c,r,hr,eq⟩
    obtain ⟨b,hb⟩ := O.valuation_surjective r
    have bn : b ≠ 0 := (map_ne_zero O.valuation).1 (hb.symm ▸ hr)
    let v : SortedAssignment Z V := fieldTupleAssignment ![c,b]
    refine ⟨v,bn,?_⟩
    intro a
    change _ ↔ a .vf 0 ∈ openDisc O c (O.valuation b)
    rw [hb]
    exact eq a
  · rintro ⟨v,nz,eq⟩
    exact ⟨v .vf 0,_,(map_ne_zero O.valuation).2 nz,eq⟩

theorem unary_point_fiber_definable
    (D : Set (SortedAssignment Z (SumVariables P U)))
    (defD : SortedDefinableOver 𝓜 S.carrier D) :
    SortedDefinableOver 𝓜 S.carrier {p | ∃ c : K,
      ∀ a : fieldAssignment 1 Z, appendAssignments p a ∈ D ↔ a .vf 0 = c} := by
  let T := SumVariables (SumVariables P U) U
  let take (s : TCsort) : SumVariables P U s → T s := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have point := SortedDefinableOver.coordinate_eq (M := 𝓜) (A := S.carrier) (Var := T)
    .vf (.inr 0) (.inl (.inr 0))
  have agree := unary_fiber_equal_definable O hO power S (defD.pullback_relabel take) point
  convert definable_project_mixed agree using 1
  ext p
  have relabel (c a : fieldAssignment 1 Z) :
      (fun s => appendAssignments (appendAssignments p c) a s ∘ take s) = appendAssignments p a := by
    funext s i
    rcases i with i | i <;> rfl
  change (∃ c : K, ∀ a : fieldAssignment 1 Z, appendAssignments p a ∈ D ↔ a .vf 0 = c) ↔
    ∃ c : fieldAssignment 1 Z, ∀ a : fieldAssignment 1 Z,
      (fun s => appendAssignments (appendAssignments p c) a s ∘ take s) ∈ D ↔ a .vf 0 = c .vf 0
  simp only [relabel]
  exact ⟨fun ⟨c,h⟩ => ⟨fieldTupleAssignment (fun _ => c),h⟩,fun ⟨c,h⟩ => ⟨c .vf 0,h⟩⟩

end GeneralizedEuler.Section5
