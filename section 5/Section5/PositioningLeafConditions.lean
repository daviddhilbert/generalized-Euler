module

public import Section5.DefinableOpenDiscTests
public import Section5.AffinePositioningTests
public import Section5.PositioningBranchSchemes

/-! First-order tests describe the point, constant-disc and affine-disc
leaves of a positioning map. They use no chosen centers or radii. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {P : TCsort → Type}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "U" => MixedVariables 1 Empty
local notation "PV" => SumVariables P U
local notation "PVV" => SumVariables PV U

@[expose] def positioningLeafGraph
    (D : Set (SortedAssignment Z PV)) (G : Set (SortedAssignment Z PVV)) :
    Set (SortedAssignment Z PVV) :=
  {a ∈ G | (fun s => a s ∘ Sum.inl) ∈ D}

theorem positioningLeafGraph_definable
    {D : Set (SortedAssignment Z PV)} {G : Set (SortedAssignment Z PVV)}
    (d : SortedDefinableOver 𝓜 S.carrier D) (g : SortedDefinableOver 𝓜 S.carrier G) :
    SortedDefinableOver 𝓜 S.carrier (positioningLeafGraph O D G) :=
  g.inter (d.pullback_relabel (fun _ => Sum.inl))

@[expose] def positioningLeafImage (G : Set (SortedAssignment Z PVV)) :
    Set (SortedAssignment Z PV) :=
  {a | ∃ x : fieldAssignment 1 Z, appendAssignments (appendAssignments (fun s => a s ∘ Sum.inl) x)
     (fun s => a s ∘ Sum.inr) ∈ G}

theorem positioningLeafImage_definable {G : Set (SortedAssignment Z PVV)}
    (g : SortedDefinableOver 𝓜 S.carrier G) :
    SortedDefinableOver 𝓜 S.carrier (positioningLeafImage O G) := by
  let exchange (s : TCsort) : PVV s → PVV s :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  convert definable_project_mixed (g.pullback_relabel exchange) using 1
  ext a
  apply exists_congr
  intro x
  have eq :
      appendAssignments (appendAssignments (fun s => a s ∘ Sum.inl) x) (fun s => a s ∘ Sum.inr) =
        (fun s => appendAssignments a x s ∘ exchange s) := by
    funext s j
    rcases j with (j | j) | j <;> rfl
  rw [eq]
  rfl

@[expose] def unaryOpenDiscTest (D : Set (SortedAssignment Z PV)) (p : SortedAssignment Z P) : Prop :=
  ∃ (c : K) (r : O.ValueGroup), r ≠ 0 ∧
    ∀ a : fieldAssignment 1 Z, appendAssignments p a ∈ D ↔ a .vf 0 ∈ openDisc O c r

@[expose] def unaryPointTest (D : Set (SortedAssignment Z PV)) (p : SortedAssignment Z P) : Prop :=
  ∃ c : K, ∀ a : fieldAssignment 1 Z, appendAssignments p a ∈ D ↔ a .vf 0 = c

@[expose] def positioningLeafValid
    (D : Set (SortedAssignment Z PV)) (G : Set (SortedAssignment Z PVV)) (p : SortedAssignment Z P) : Prop :=
  (∀ a : fieldAssignment 1 Z, appendAssignments p a ∉ D) ∨ unaryPointTest O D p ∨
  (unaryOpenDiscTest O D p ∧
    (constantPositioning D G p ∨
      (unaryOpenDiscTest O (positioningLeafImage O (positioningLeafGraph O D G)) p ∧
       ∃ u : RV0 O, u ≠ 0 ∧ affinePositioningSlope O (positioningLeafGraph O D G) p u)))

theorem positioningLeafValid_definable
    (F : FieldTerms (convexLanguage L)) (minusOne : L.Term Empty)
    (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {D : Set (SortedAssignment Z PV)} {G : Set (SortedAssignment Z PVV)}
    (d : SortedDefinableOver 𝓜 S.carrier D) (g : SortedDefinableOver 𝓜 S.carrier G) :
    SortedDefinableOver 𝓜 S.carrier {p | positioningLeafValid O D G p} := by
  let R := RVVariables (Fin 1)
  let T := SumVariables P R
  have empty := definable_forall_assignments d.compl
  have point := unary_point_fiber_definable O hO power S D d
  have openDisc := unary_openDisc_fiber_definable O hO power S F minusOne hm hF D d
  have graph := positioningLeafGraph_definable O hO power S d g
  have openImage := unary_openDisc_fiber_definable O hO power S F minusOne hm hF _
    (positioningLeafImage_definable O hO power S graph)
  have const := (positioning_branch_tests_definable d g).1
  have aff := affinePositioningSlope_definable O hO power S F minusOne hm hF graph
  have nonzero := (SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier)
    (Var := T) .rv (.inr 0) rvZeroTerm).compl
  have scaled : SortedDefinableOver 𝓜 S.carrier {p : SortedAssignment Z P |
      ∃ u : RV0 O, u ≠ 0 ∧ affinePositioningSlope O (positioningLeafGraph O D G) p u} := by
    convert definable_project_mixed (nonzero.inter aff) using 1
    ext p
    have ev (v : SortedAssignment Z R) :
        (rvZeroTerm : SortedTerm L E (WithBase S.carrier T) .rv).realize 𝓜
          (fun s => Sum.elim Subtype.val (appendAssignments p v s)) = 0 := realize_rvZeroTerm O hO power _
    simp only [Set.mem_inter_iff,Set.mem_compl_iff]
    change (∃ u : RV0 O, u ≠ 0 ∧ affinePositioningSlope O (positioningLeafGraph O D G) p u) ↔
      ∃ v : SortedAssignment Z R,
        v .rv 0 ≠ (rvZeroTerm : SortedTerm L E (WithBase S.carrier T) .rv).realize 𝓜
          (fun s => Sum.elim Subtype.val (appendAssignments p v s)) ∧
        affinePositioningSlope O (positioningLeafGraph O D G) (fun s => appendAssignments p v s ∘ Sum.inl) (v .rv 0)
    have left (v : SortedAssignment Z R) : (fun s => appendAssignments p v s ∘ Sum.inl) = p := by
      funext s i
      rfl
    simp only [ev,left]
    exact ⟨fun ⟨u,hn,h⟩ => ⟨rvTupleAssignment (fun _ => u),hn,h⟩,fun ⟨v,hn,h⟩ => ⟨v .rv 0,hn,h⟩⟩
  exact empty.union (point.union (openDisc.inter (const.union (openImage.inter scaled))))

end GeneralizedEuler.Section5
