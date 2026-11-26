module

public import Section5.FieldPairTranslationRuns
public import Section5.ScaledPairLabels
public import Section5.PositionedCellClassification
import all Section3.AffineSlopes

/-! The two contraction orders on a named balanced cell have equal
terminal graded RV classes. This includes the graph with zero paradigm. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem balanced_cell_contraction_runs
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (a b : S.carrier .vf) (rA rB : O.ValueGroup)
    (ha : rA ≠ 0) (f g : K → K) (t t' u₀ : S.carrier .rv) (u : RV O)
    (hu : u₀.val = (u : RV0 O)) (ht' : t'.val = oppositeParadigm O t.val u)
    (affine : RVAffineOn O (openDisc O a.val rA) f u)
    (dtd : DiscToDiscOn O (openDisc O a.val rA) (openDisc O b.val rB) f g)
    (center : f a.val = b.val) (small : unsignedValue O t.val < rB)
    (defC : SortedDefinableOver 𝓜 S.carrier
      (fieldPairAssignment O ⁻¹' positionedCell O (openDisc O a.val rA) f t.val))
    (defF : DefinableRelation 𝓜 S.carrier (fun (x y : fieldAssignment 1 Z) =>
      x .vf 0 ∈ openDisc O a.val rA ∧ f (x .vf 0) = y .vf 0))
    (defG : DefinableRelation 𝓜 S.carrier (fun (x y : fieldAssignment 1 Z) =>
      x .vf 0 ∈ openDisc O b.val rB ∧ g (x .vf 0) = y .vf 0))
    (zero : S.carrier .rv) (hz : zero.val = 0) :
    let A := RetainedFieldFamily.fieldPairSet hO power S _ defC
    ∃ (U V : RetainedFieldFamily 𝓜 S 0 2) (idx : Fin 2 ≃ U.tags) (idy : Fin 2 ≃ V.tags),
      HeadContractionRun A U ∧
      HeadContractionRun (A.permuteVF (Equiv.swap 0 1)) V ∧
      U.terminalGradedClass idx zero hz = V.terminalGradedClass idy zero hz := by
  classical
  intro A
  let D := openDisc O a.val rA
  let E' := openDisc O b.val rB
  let C := positionedCell O D f t.val
  let W := A.permuteVF (Equiv.swap 0 1)
  let f' (x : K) := if x ∈ D then f x else a.val
  let g' (y : K) := if y ∈ E' then g y else b.val
  have graphF : DefinableRelation 𝓜 S.carrier (fun (x y : fieldAssignment 1 Z) => f' (x .vf 0) = y .vf 0) :=
    named_total_field_graph D f a defF
  have graphG : DefinableRelation 𝓜 S.carrier (fun (x y : fieldAssignment 1 Z) => g' (x .vf 0) = y .vf 0) :=
    named_total_field_graph E' g b defG
  have h₁ : ∀ x q (p : W.tags → RV0 O),
      (x,q,p) ∈ W.verticalCarrier ↔ q 0 ∈ D ∧ rv O (x-f' (q 0)) = t.val := by
    intro x q p
    have hp := RetainedFieldFamily.fieldPairSet_swapped_vertical hO power S C defC x q p
    refine hp.trans ?_
    change (q 0 ∈ D ∧ rv O (x-f (q 0)) = t.val) ↔ _
    exact and_congr_right (fun h => by rw [show f' (q 0) = f (q 0) from ite_eq_left h])
  have image : f '' D = E' := dtd.1.image_eq
  have radius := oppositeParadigm_small_of_target_radius O ha affine image small
  have target (p : K × K) (hp : p ∈ C) : p.2 ∈ E' := by
    have h := dtd.1.mapsTo hp.1
    change p.2 ∈ openDisc O b.val rB
    rw [← openDisc_change_center O h]
    change O.valuation (p.2 - f p.1) < rB
    rw [← unsignedValue_rv,show rv O (p.2-f p.1) = t.val from hp.2]
    exact small
  have inv (y : K) (hy : y ∈ E') : g y ∈ D ∧ f (g y) = y := by
    obtain ⟨x,hx,he⟩ := dtd.1.surjOn hy
    have eq := (congrArg g he).symm.trans (dtd.2.1.1 hx)
    exact ⟨eq.symm ▸ hx,dtd.2.1.2 hy⟩
  have forward := positionedCell_translate_first O E' affine radius target inv
  have h₂ : ∀ x q (p : A.tags → RV0 O),
      (x,q,p) ∈ A.verticalCarrier ↔ q 0 ∈ E' ∧ rv O (x-g' (q 0)) = t'.val := by
    intro x q p
    refine (RetainedFieldFamily.fieldPairSet_vertical hO power S C defC x q p).trans ?_
    let y := q 0
    constructor
    · intro h
      have hy := target (x,y) h
      have full : (x - g y,y) ∈ (rv O ⁻¹' {oppositeParadigm O t.val u}) ×ˢ E' :=
        forward ▸ Set.mem_image_of_mem (fun p : K × K => (p.1 - g p.2,p.2)) h
      exact ⟨hy,by rw [show g' y = g y from ite_eq_left hy,ht']; exact full.1⟩
    · rintro ⟨hy,hv⟩
      have hr : rv O (x - g y) = oppositeParadigm O t.val u := by
        rw [show g' y = g y from ite_eq_left hy,ht'] at hv
        exact hv
      have full : (x - g y,y) ∈ (rv O ⁻¹' {oppositeParadigm O t.val u}) ×ˢ E' := ⟨hr,hy⟩
      obtain ⟨z,hz',e⟩ := forward.symm ▸ full
      have second : z.2 = y := congrArg Prod.snd e
      have first : z.1 = x := sub_left_inj.mp (by simpa only [second] using congrArg Prod.fst e)
      exact (Prod.ext first second : z = (x,y)) ▸ hz'
  let stabA := centered_disc_stable (O := O) a.val rA
  let stabB := centered_disc_stable (O := O) b.val rB
  let U := HeadContractionData.centeredTail F minusOne hm hF A E' g' t'.val graphG h₂ b stabB
  let V := HeadContractionData.centeredTail F minusOne hm hF W D f' t.val graphF h₁ a stabA
  have emptyA : IsEmpty A.tags := by change IsEmpty Empty; infer_instance
  have emptyW : IsEmpty W.tags := emptyA
  let iu := HeadContractionData.positionTerminalTags F minusOne hm hF A E' g' t'.val graphG h₂ b stabB emptyA
  let iv := HeadContractionData.positionTerminalTags F minusOne hm hF W D f' t.val graphF h₁ a stabA emptyW
  refine ⟨U.target,V.target,iu,iv,
    HeadContractionData.position_translation_run _ _ _ _ _ _ _ _ _ _ _ _,
    HeadContractionData.position_translation_run _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
  symm
  let X := (fun x : K => rv O (x-a.val)) '' D
  let Y := (fun y : K => rv O (y-b.val)) '' E'
  have range : (fun v => u₀.val * v) '' X = Y := by
    ext v
    constructor
    · rintro ⟨w,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨f x,dtd.1.mapsTo hx,?_⟩
      rw [← center,hu]
      exact affine x hx a.val (mem_openDisc_center O ha a.val)
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,hx,rfl⟩ := dtd.1.surjOn hy
      refine ⟨_,Set.mem_image_of_mem _ hx,?_⟩
      rw [← center,hu]
      exact (affine x hx a.val (mem_openDisc_center O ha a.val)).symm
  apply scaled_pair_terminal_classes V.target U.target iv iu t t' u₀ (fun h => WithZero.coe_ne_zero (hu.symm.trans h))
    (by rw [ht',opposite_paradigm_zero_iff]) X Y
  · exact HeadContractionData.position_terminal_labels F minusOne hm hF W D f' t.val graphF h₁ a stabA emptyW
  · exact HeadContractionData.position_terminal_labels F minusOne hm hF A E' g' t'.val graphG h₂ b stabB emptyA
  · exact range
  · exact HeadContractionData.position_terminal_select F minusOne hm hF W D f' t.val graphF h₁ a stabA emptyW
  · exact HeadContractionData.position_terminal_select F minusOne hm hF A E' g' t'.val graphG h₂ b stabB emptyA

end GeneralizedEuler.Section5
