module

public import Section4.TaggedMatchGraph
public import Section4.ResidueBaseValues
public import Section4.SignedValueGeneration
import all Section4.SignedValueGeneration
import all Section4.SignedRectangleFactors
import all Section4.TaggedMatchGraph
import all Section2.RVCoordinatePrimitives
import all Section2.RVFormulaSeparation
import all Section2.RVSplitCoordinates
import all Section2.SignedValue
import all Section2.RVMonomials

/-! A fixed-base definable pullback on signed values is definable in
the signed value language. Slicing at a residue representative of each
sign recovers all sign components. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
  (hO : IsOrderConvex O)

theorem signedLabel_coe {t : RV0 O} (nz : t ≠ 0) :
    (↑(signedLabel O hO t) : WithZero (SignedValueGroup O)) = signedValue O hO t := by
  cases h : signedValue O hO t using WithZero.recZeroCoe with
  | zero => exact ((map_ne_zero _).mpr nz h).elim
  | coe u => simp [signedLabel,h]

theorem signedLabel_rep (α : SignedValueGroup O) :
    ∃ t : RV0 O, t ≠ 0 ∧ signedLabel O hO t = α := by
  obtain ⟨t,ht⟩ := signedValueUnit_surjective O hO α
  refine ⟨(t : RV0 O),WithZero.coe_ne_zero,?_⟩
  apply WithZero.coe_injective
  rw [signedLabel_coe O hO WithZero.coe_ne_zero]
  exact congrArg (fun p : SignedValueGroup O => (p : WithZero (SignedValueGroup O))) ht

theorem signedLabel_mul {t u : RV0 O} (ht : t ≠ 0) (hu : u ≠ 0) :
    signedLabel O hO (t*u) = signedLabel O hO t * signedLabel O hO u := by
  apply WithZero.coe_injective
  rw [signedLabel_coe O hO (mul_ne_zero ht hu),map_mul,WithZero.coe_mul,signedLabel_coe O hO ht,signedLabel_coe O hO hu]

theorem residue_for_sign (b : SignTypeˣ) :
    ∃ r : Residue O, r ≠ 0 ∧ signedLabel O hO (residueRV O r) = (b,1) := by
  obtain ⟨t,nt,ht⟩ := signedLabel_rep O hO (b,1)
  have val : unsignedValue O t = 1 := (unsignedValue_of_signedLabel O hO t nt).trans (by rw [ht]; rfl)
  obtain ⟨r,hr⟩ := (show t ∈ Set.range (residueRV O) by rw [range_residueRV]; exact Or.inr val)
  exact ⟨r,fun hz => nt (hr.symm.trans (hz ▸ residueRV_zero O)),hr ▸ ht⟩

variable {E : Type*} {J JG JH JS : Language} [J.Structure K] [J.Structure (Residue O)]
  [JG.Structure O.ValueGroupˣ] [JH.Structure (Residue O)] [JS.Structure (SignedValueGroup O)]
  (P : E → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

theorem signed_label_fiber_relation (k : ℕ) : isRVSet _ S
    {p : Fin k ⊕ Fin k → RV0 O | (∀ i, p (.inr i) ≠ 0) ∧
      signedLabel O hO ∘ p ∘ Sum.inr = signedLabel O hO ∘ p ∘ Sum.inl} := by
  -- The dummy label at zero is one, so test the zero input separately.
  let V := RVVariables (Fin k ⊕ Fin k)
  let Var := fun s => (S.carrier s : Type _) ⊕ V s
  let x (i : Fin k) : SortedTerm J E Var .rv := .var (.inr (.inr i))
  let y (i : Fin k) : SortedTerm J E Var .rv := .var (.inr (.inl i))
  let one : SortedTerm J E Var .rv := rvOneTerm
  let zero : SortedTerm J E Var .rv := rvZeroTerm
  let row (i : Fin k) := ((SortedFormula.equal (x i) zero).neg).conjunction
    ((rvSameSignedValueFormula (x i) (y i)).disjunction
      ((SortedFormula.equal (y i) zero).conjunction (rvSameSignedValueFormula (x i) one)))
  have hr (i : Fin k) : isRVSet _ S {p : Fin k ⊕ Fin k → RV0 O |
      p (.inr i) ≠ 0 ∧ signedLabel O hO (p (.inr i)) = signedLabel O hO (p (.inl i))} := by
    refine ⟨row i,fun w => ?_⟩
    simp only [row,SortedFormula.realize_conjunction,SortedFormula.realize_disjunction,SortedFormula.realize_neg,
      realize_rvSameSignedValueFormula,SortedFormula.realize,SortedTerm.realize,x,y,one,zero,rvOneTerm,rvZeroTerm]
    change (_ ∧ _) ↔ (_ ∧ (signedValue O hO _ = signedValue O hO _ ∨ _ = 0 ∧ signedValue O hO _ = signedValue O hO 1))
    apply and_congr_right; intro nx
    change signedLabel O hO (w .rv (.inr i)) = signedLabel O hO (w .rv (.inl i)) ↔ signedValue O hO (w .rv (.inr i)) = signedValue O hO (w .rv (.inl i)) ∨ w .rv (.inl i) = 0 ∧ signedValue O hO (w .rv (.inr i)) = signedValue O hO 1
    by_cases ny : w .rv (.inl i) = 0
    · have sn : signedValue O hO (w .rv (.inr i)) ≠ 0 := (signedLabel_coe O hO nx).symm ▸ WithZero.coe_ne_zero
      have zl : signedLabel O hO 0 = 1 := by simp [signedLabel]
      rw [ny,zl,map_zero,map_one]
      simp only [sn,false_or,true_and]
      rw [← signedLabel_coe O hO nx]
      exact WithZero.coe_inj.symm
    · rw [← signedLabel_coe O hO nx,← signedLabel_coe O hO ny]
      simp only [ny,false_and,or_false,WithZero.coe_inj]
  unfold isRVSet
  convert SortedDefinableOver.iInter hr using 1
  ext w; simp [funext_iff,forall_and]

theorem signed_value_reflection (T : RVValueSection O) (G : Set O.ValueGroupˣ) (B : Set (Residue O))
    (A : Set (SignedValueGroup O)) (interpret : SignedInterpretation (J := JG) (H := JS) G A)
    (p : E → O.ValueGroupˣ → O.ValueGroupˣ) (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO G B p P)
    (g : E → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (clamp : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
    (hsec : ∀ e γ, P e (T.representative γ) = T.representative (p e γ))
    {I : Type} [Fintype I] (D : Set (I → SignedValueGroup O))
    (qe : ∀ φ : SortedFormula J E (FullRVVariables S I), ∃ q : SortedFormula J E (FullRVVariables S I), q.IsQF ∧
      ∀ w, q.realize (canonicalStructure (L := J) O hO P) w ↔ φ.realize (canonicalStructure (L := J) O hO P) w)
    (base : ∀ t : S.carrier .rv, (T.encode t.val).1 ∈ G ∧ (T.encode t.val).2 ∈ B)
    (hd : isRVSet _ S (tupleSharp (M := canonicalStructure (L := J) O hO P) (signedLabel O hO) I D)) :
    A.Definable JS D := by
  let Q := T.canonicalCoordinatePresentation primitives g agrees clamp units hsec
  have sep := Q.separated_rv_pullback S hd qe base (T.separated_decoded_coordinate_graph primitives)
  apply (interpret D).mpr; intro b
  choose r nr sign using fun i => residue_for_sign O hO (b i)
  have slice := SeparatedSets.slice (Set.definable_empty (A := G) (L := JG)) (fun a c => a.union c) r sep
  convert slice using 1
  apply Set.ext; intro y
  change signInsert b y ∈ D ↔ (∀ i, T.join (y i) (r i) ≠ 0) ∧ (signedLabel O hO ∘ fun i => T.join (y i) (r i)) ∈ D
  have label : (signedLabel O hO ∘ fun i => T.join (y i) (r i)) = signInsert b y := by
    funext i
    have nz : residueRV O (r i) ≠ 0 := fun eq => nr i (residueRV_injective O (eq.trans (residueRV_zero O).symm))
    change signedLabel O hO (T.representative (y i) * residueRV O (r i)) = (b i,y i)
    rw [signedLabel_mul O hO (T.representative_ne_zero _) nz,sign i]
    have pos := signedLabel_code O hO (T.lift (y i))
    change signedLabel O hO (T.representative (y i)) = (1,positiveValueMap O (T.lift (y i))) at pos
    rw [pos,T.value_lift]; simp
  rw [label]
  exact ⟨fun h => ⟨fun i => T.join_ne_zero _ (nr i),h⟩,And.right⟩

end GeneralizedEuler.Section4
