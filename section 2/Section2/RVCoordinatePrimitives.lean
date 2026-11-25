module

public import Section2.RVSplitCoordinates
public import Section2.RVFormulaSeparation

/-! The primitive graphs in the separated value and residue languages. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w u' v' u'' v'' a

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} {L : Language.{u, v}} [L.Structure (Residue O)] {E : Type w}
  {JG : Language.{u', v'}} {JH : Language.{u'', v''}}
  [JG.Structure O.ValueGroupˣ] [JH.Structure (Residue O)]
  {A : Set O.ValueGroupˣ} {B : Set (Residue O)}

/-- The fixed-base operations used on the two coordinate axes. The
value-language input uses multiplication for addition in the exponent
module. The residue power is the restriction of the named RV power. -/
structure RVCoordinateDefinability (hO : IsOrderConvex O)
    (A : Set O.ValueGroupˣ) (B : Set (Residue O))
    (p : E → O.ValueGroupˣ → O.ValueGroupˣ) (P : E → RV0 O → RV0 O) : Prop where
  value_one : 1 ∈ A
  residue_zero : 0 ∈ B
  residue_one : 1 ∈ B
  value_mul : A.Definable JG (coordinateTermGraph (fun x : Fin 2 → O.ValueGroupˣ => x 0 * x 1))
  value_inv : A.Definable JG (coordinateTermGraph (fun x : Unit → O.ValueGroupˣ => (x ())⁻¹))
  value_lt : A.Definable JG {x : Fin 2 → O.ValueGroupˣ | (x 0 : O.ValueGroup) < x 1}
  value_power : ∀ e, A.Definable JG (coordinateTermGraph (fun x : Unit → O.ValueGroupˣ => p e (x ())))
  residue_mul : B.Definable JH (coordinateTermGraph (fun x : Fin 2 → Residue O => x 0 * x 1))
  residue_inv : B.Definable JH (coordinateTermGraph (fun x : Unit → Residue O => (x ())⁻¹))
  residue_lt : letI := residueLinearOrder O hO
    B.Definable JH {x : Fin 2 → Residue O | x 0 < x 1}
  residue_pos : letI := residueLinearOrder O hO
    B.Definable JH {x : Unit → Residue O | 0 < x ()}
  residue_neg : letI := residueLinearOrder O hO
    B.Definable JH {x : Unit → Residue O | x () < 0}
  residue_power : ∀ e, B.Definable JH
    (coordinateTermGraph (fun x : Unit → Residue O => rvResidue O (P e (residueRV O (x ())))))
  residue_function : ∀ {n} (f : L.Functions n),
    B.Definable JH (coordinateTermGraph (Language.Structure.funMap f))

namespace RVValueSection

variable (S : RVValueSection O)

@[expose]
def encode (t : RV0 O) : O.ValueGroupˣ × Residue O :=
  (valueCoordinate t, S.residueCoordinate t)

@[simp] theorem encode_zero : S.encode 0 = (1, 0) := by
  simp only [encode, valueCoordinate_zero, S.residueCoordinate_zero]

@[simp] theorem encode_one : S.encode 1 = (1, 1) := by
  rw [← residueRV_one O, encode, valueCoordinate_residueRV, S.residueCoordinate_residueRV]

variable {hO : IsOrderConvex O} {p : E → O.ValueGroupˣ → O.ValueGroupˣ} {P : E → RV0 O → RV0 O}
  (D : RVCoordinateDefinability (L := L) (JG := JG) (JH := JH) hO A B p P)

include D

private theorem separated_value_one {I : Type a} (i : I) :
    SplitDefinable JG JH A B {x : SplitAssignment O.ValueGroupˣ (Residue O) I | x.1 i = 1} :=
  SplitDefinable.leftCylinder (SplitDefinable.definable_coordinate_eq_param i ⟨1, D.value_one⟩)

private theorem separated_residue_zero {I : Type a} (i : I) :
    SplitDefinable JG JH A B {x : SplitAssignment O.ValueGroupˣ (Residue O) I | x.2 i = 0} :=
  SplitDefinable.rightCylinder (SplitDefinable.definable_coordinate_eq_param i ⟨0, D.residue_zero⟩)

private theorem separated_encoded_zero {I : Type a} :
    SplitDefinable JG JH A B (splitTermGraph (fun _ : SplitAssignment O.ValueGroupˣ (Residue O) I =>
      (1, 0))) :=
  SplitDefinable.graph_constant ⟨1, D.value_one⟩ ⟨0, D.residue_zero⟩

private theorem separated_encoded_one {I : Type a} :
    SplitDefinable JG JH A B (splitTermGraph (fun _ : SplitAssignment O.ValueGroupˣ (Residue O) I =>
      (1, 1))) :=
  SplitDefinable.graph_constant ⟨1, D.value_one⟩ ⟨1, D.residue_one⟩

theorem separated_mul_graph :
    SplitDefinable JG JH A B (splitTermGraph
      (fun x : SplitAssignment O.ValueGroupˣ (Residue O) (Fin 2) =>
        S.encode (S.join (x.1 0) (x.2 0) * S.join (x.1 1) (x.2 1)))) := by
  classical
  let active : Set (SplitAssignment O.ValueGroupˣ (Residue O) (Fin 2)) :=
    {x | x.2 0 ≠ 0 ∧ x.2 1 ≠ 0}
  have hactive : SplitDefinable JG JH A B active :=
    SplitDefinable.inter (SplitDefinable.compl (separated_residue_zero D 0))
      (SplitDefinable.compl (separated_residue_zero D 1))
  have h := SplitDefinable.graph_piecewise hactive
    (SplitDefinable.graph_pair D.value_mul D.residue_mul) (separated_encoded_zero D)
  convert h using 1
  congr 1
  funext x
  rw [S.join_mul]
  by_cases hx : x ∈ active
  · rw [ite_eq_left hx, encode, S.valueCoordinate_join _ (mul_ne_zero hx.1 hx.2),
      S.residueCoordinate_join]
  · have hv : x.2 0 * x.2 1 = 0 := by
      by_contra hv
      exact hx ⟨fun h0 => hv (by rw [h0, zero_mul]), fun h1 => hv (by rw [h1, mul_zero])⟩
    rw [ite_eq_right hx, hv, S.join_zero, encode, valueCoordinate_zero, S.residueCoordinate_zero]

theorem separated_inv_graph :
    SplitDefinable JG JH A B (splitTermGraph
      (fun x : SplitAssignment O.ValueGroupˣ (Residue O) Unit =>
        S.encode (S.join (x.1 ()) (x.2 ()))⁻¹)) := by
  classical
  let active : Set (SplitAssignment O.ValueGroupˣ (Residue O) Unit) := {x | x.2 () ≠ 0}
  have hactive : SplitDefinable JG JH A B active :=
    SplitDefinable.compl (separated_residue_zero D ())
  have h := SplitDefinable.graph_piecewise hactive
    (SplitDefinable.graph_pair D.value_inv D.residue_inv) (separated_encoded_zero D)
  convert h using 1
  congr 1
  funext x
  rw [S.join_inv]
  by_cases hx : x ∈ active
  · rw [ite_eq_left hx, encode, S.valueCoordinate_join _ (inv_ne_zero hx), S.residueCoordinate_join]
  · have hv : x.2 () = 0 := not_not.mp hx
    rw [ite_eq_right hx, hv, inv_zero, S.join_zero, encode, valueCoordinate_zero, S.residueCoordinate_zero]

theorem separated_residue_graph {n : ℕ} (f : L.Functions n) :
    SplitDefinable JG JH A B (splitTermGraph
      (fun x : SplitAssignment O.ValueGroupˣ (Residue O) (Fin n) =>
        S.encode (extendResidueOperation O (Language.Structure.funMap f)
          (fun i => S.join (x.1 i) (x.2 i))))) := by
  classical
  let active : Set (SplitAssignment O.ValueGroupˣ (Residue O) (Fin n)) := {x | ∀ i, x.1 i = 1 ∨ x.2 i = 0}
  have hactive : SplitDefinable JG JH A B active := by
    have h := SplitDefinable.iInter (fun i : Fin n =>
      (separated_value_one D i).union (separated_residue_zero D i))
    convert h using 1
    ext x
    simp only [active, Set.mem_ofPred, Set.mem_iInter, Set.mem_union]
  have h := SplitDefinable.graph_piecewise hactive
    (SplitDefinable.graph_pair (SplitDefinable.coordinateTermGraph_const ⟨1, D.value_one⟩)
      (D.residue_function f)) (separated_encoded_zero D)
  convert h using 1
  congr 1
  funext x
  rw [S.extendResidueOperation_join_with_zero]
  by_cases hx : x ∈ active
  · have hg : ∀ i, x.1 i = 1 ∨ x.2 i = 0 := hx
    rw [ite_eq_left hx, ite_eq_left hg, encode, valueCoordinate_residueRV, S.residueCoordinate_residueRV]
  · have hg : ¬∀ i, x.1 i = 1 ∨ x.2 i = 0 := hx
    rw [ite_eq_right hx, ite_eq_right hg, S.encode_zero]

theorem separated_decoded_coordinate_graph {I : Type a} (i : I) :
    SplitDefinable JG JH A B (splitTermGraph
      (fun x : SplitAssignment O.ValueGroupˣ (Residue O) I => S.encode (S.join (x.1 i) (x.2 i)))) := by
  classical
  have h := SplitDefinable.graph_piecewise (separated_residue_zero D i)
    (separated_encoded_zero D) (SplitDefinable.graph_coordinate i)
  convert h using 1
  congr 1
  funext x
  by_cases hx : x ∈ {z : SplitAssignment O.ValueGroupˣ (Residue O) I | z.2 i = 0}
  · have hv : x.2 i = 0 := hx
    rw [ite_eq_left hx, hv, S.join_zero, S.encode_zero]
  · have hv : x.2 i ≠ 0 := hx
    rw [ite_eq_right hx, encode, S.valueCoordinate_join _ hv, S.residueCoordinate_join]

set_option linter.style.haveILetI false in
theorem separated_power_graph (e : E) {g : PositiveField K →* PositiveField K}
    (hP : AgreesWithFieldPower O g (P e))
    (hclamp : ∀ t, ¬IsPositiveRV O t → P e t = 0)
    (hunit : ∀ x : PositiveField K, O.valuation (x : K) = 1 → O.valuation (g x : K) = 1)
    (hsection : ∀ γ, P e (S.representative γ) = S.representative (p e γ)) :
    SplitDefinable JG JH A B (splitTermGraph
      (fun x : SplitAssignment O.ValueGroupˣ (Residue O) Unit =>
        S.encode (P e (S.join (x.1 ()) (x.2 ()))))) := by
  classical
  letI := residueLinearOrder O hO
  letI := rvLinearOrder O hO
  let active : Set (SplitAssignment O.ValueGroupˣ (Residue O) Unit) := {x | 0 < x.2 ()}
  have hactive : SplitDefinable JG JH A B active := SplitDefinable.rightCylinder D.residue_pos
  have h := SplitDefinable.graph_piecewise hactive
    (SplitDefinable.graph_pair (D.value_power e) (D.residue_power e)) (separated_encoded_zero D)
  convert h using 1
  congr 1
  funext x
  by_cases hx : x ∈ active
  · have hr : 0 < x.2 () := hx
    have hj := S.leadingTermPower_join_positive hO hP hunit (p e) hsection (x.1 ()) (x.2 ()) hr
    have hv : rvResidue O (P e (residueRV O (x.2 ()))) ≠ 0 := by
      have hp := leadingTermPower_pos O hP ((isPositiveRV_iff_pos O hO).mpr
        ((S.join_pos_iff hO (x.1 ()) (x.2 ())).mpr hr))
      intro h0
      rw [hj, h0, S.join_zero] at hp
      exact ((isPositiveRV_iff_pos O hO).mp hp).false
    rw [ite_eq_left hx, hj, encode, S.valueCoordinate_join _ hv, S.residueCoordinate_join]
  · have hn : x.2 () ≤ 0 := le_of_not_gt hx
    rw [ite_eq_right hx, S.leadingTermPower_join_nonpositive hO (P e) hclamp _ _ hn,
      encode, valueCoordinate_zero, S.residueCoordinate_zero]

theorem separated_isResidueNonzero :
    SplitDefinable JG JH A B {x : SplitAssignment O.ValueGroupˣ (Residue O) Unit |
      unsignedValue O (S.join (x.1 ()) (x.2 ())) = 1} := by
  have h := SplitDefinable.inter (separated_value_one D ()) (SplitDefinable.compl (separated_residue_zero D ()))
  convert h using 1
  ext x
  rw [Set.mem_ofPred, S.unsignedValue_eq_one_iff_coordinates, S.residueCoordinate_join]
  change valueCoordinate (S.join (x.1 ()) (x.2 ())) = 1 ∧ x.2 () ≠ 0 ↔ x.1 () = 1 ∧ x.2 () ≠ 0
  exact ⟨fun ⟨h, hn⟩ => ⟨(S.valueCoordinate_join _ hn).symm.trans h, hn⟩,
    fun ⟨h, hn⟩ => ⟨(S.valueCoordinate_join _ hn).trans h, hn⟩⟩

set_option linter.style.haveILetI false in
theorem separated_order :
    letI := rvLinearOrder O hO
    SplitDefinable JG JH A B {x : SplitAssignment O.ValueGroupˣ (Residue O) (Fin 2) |
      S.join (x.1 0) (x.2 0) ≤ S.join (x.1 1) (x.2 1)} := by
  letI := rvLinearOrder O hO
  letI := residueLinearOrder O hO
  let Full := SplitAssignment O.ValueGroupˣ (Residue O) (Fin 2)
  let Pos (i : Fin 2) : Set Full := {x | 0 < x.2 i}
  let Neg (i : Fin 2) : Set Full := {x | x.2 i < 0}
  let Lt : Set Full := {x | (x.1 0 : O.ValueGroup) < x.1 1}
  let Gt : Set Full := {x | (x.1 1 : O.ValueGroup) < x.1 0}
  let Same : Set Full := {x | x.1 0 = x.1 1}
  let ResLE : Set Full := {x | x.2 0 ≤ x.2 1}
  let flip : Fin 2 → Fin 2 := Fin.cases 1 (fun _ => 0)
  have hPos (i : Fin 2) : SplitDefinable JG JH A B (Pos i) :=
    SplitDefinable.rightCylinder (D.residue_pos.preimage_comp (fun _ : Unit => i))
  have hNeg (i : Fin 2) : SplitDefinable JG JH A B (Neg i) :=
    SplitDefinable.rightCylinder (D.residue_neg.preimage_comp (fun _ : Unit => i))
  have hl : SplitDefinable JG JH A B Lt := SplitDefinable.leftCylinder D.value_lt
  have hg : SplitDefinable JG JH A B Gt := SplitDefinable.leftCylinder (D.value_lt.preimage_comp flip)
  have he : SplitDefinable JG JH A B Same :=
    SplitDefinable.leftCylinder (SplitDefinable.definable_coordinate_eq 0 1)
  have hr : SplitDefinable JG JH A B ResLE := by
    have h := SplitDefinable.compl (JG := JG) (A := A)
      (SplitDefinable.rightCylinder (D.residue_lt.preimage_comp flip))
    convert h using 1
    ext x
    simp only [ResLE, Set.mem_ofPred, Set.mem_compl_iff, Set.mem_preimage, Function.comp_apply,
      flip, Fin.cases_zero, not_lt]
    rfl
  let sameOrder := he.inter hr
  have h := ((hPos 0).compl.inter (hNeg 1).compl).union
    ((((hPos 0).inter (hPos 1)).inter (hl.union sameOrder)).union
      (((hNeg 0).inter (hNeg 1)).inter (hg.union sameOrder)))
  convert h using 1
  ext x
  rw [Set.mem_ofPred, S.join_le_join_iff_coordinates hO]
  simp only [Pos, Neg, Lt, Gt, Same, ResLE, Set.mem_compl_iff, Set.mem_inter_iff,
    Set.mem_union, and_assoc]
  change _ ↔ (¬0 < x.2 0 ∧ ¬x.2 1 < 0) ∨
    (0 < x.2 0 ∧ 0 < x.2 1 ∧ ((x.1 0 : O.ValueGroup) < x.1 1 ∨ (x.1 0 = x.1 1 ∧ x.2 0 ≤ x.2 1))) ∨
    (x.2 0 < 0 ∧ x.2 1 < 0 ∧ ((x.1 1 : O.ValueGroup) < x.1 0 ∨ (x.1 0 = x.1 1 ∧ x.2 0 ≤ x.2 1)))
  rw [not_lt, not_lt]

set_option linter.style.haveILetI false in
/-- Every canonical RV primitive has a separated interpretation in
the fixed coordinate reducts. -/
def canonicalCoordinatePresentation [L.Structure K]
    (g : E → PositiveField K →* PositiveField K)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hclamp : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
    (hsection : ∀ e γ, P e (S.representative γ) = S.representative (p e γ)) :
    RVCoordinatePresentation (canonicalStructure (L := L) O hO P) JG JH A B where
  encode := S.encode
  decode := fun x => S.join x.1 x.2
  decode_encode := S.join_coordinates
  function_graph := by
    intro ss f hs
    cases f with
    | rvZero =>
      change SplitDefinable JG JH A B (splitTermGraph (fun _ : SplitAssignment _ _ (Fin 0) => S.encode 0))
      rw [S.encode_zero]
      exact separated_encoded_zero D
    | rvOne =>
      change SplitDefinable JG JH A B (splitTermGraph (fun _ : SplitAssignment _ _ (Fin 0) => S.encode 1))
      rw [S.encode_one]
      exact separated_encoded_one D
    | rvMul => exact S.separated_mul_graph D
    | rvInv =>
      exact SplitDefinable.graph_relabel (fun _ : Unit => (0 : Fin 1)) (S.separated_inv_graph D)
    | power e =>
      exact SplitDefinable.graph_relabel (fun _ : Unit => (0 : Fin 1))
        (S.separated_power_graph D e (hP e) (hclamp e) (hunit e) (hsection e))
    | @residue n f =>
      let cast := Fin.cast (List.length_replicate (n := n) (a := TCsort.rv)).symm
      have h := SplitDefinable.graph_relabel cast (S.separated_residue_graph D f)
      convert h using 1
      congr 1
      funext x
      change S.encode (extendResidueOperation O (Language.Structure.funMap f)
        (homogeneousArgs (X := CanonicalSort O) (s := .rv) (n := n)
          (fun i => (hs i).symm ▸ S.join (x.1 i) (x.2 i)))) = _
      rw [homogeneousArgs_of_cast hs]
      rfl
    | rv =>
      have h : TCsort.vf = TCsort.rv := hs 0
      cases h
  relation := by
    intro ss r hs
    let M := canonicalStructure (L := L) O hO P
    cases r with
    | residueNonzero =>
      exact (S.separated_isResidueNonzero D).preimage_relabel (fun _ : Unit => (0 : Fin 1))
    | rvLE => exact S.separated_order D
    | @vf n r =>
      have empty (i : Fin (List.replicate n TCsort.vf).length) : False := by
        have h := hs i
        simp [List.get_eq_getElem] at h
      let args : SortedArgs (CanonicalSort O) (List.replicate n .vf) := fun i => (empty i).elim
      have hEq (x : SplitAssignment O.ValueGroupˣ (Residue O) (Fin (List.replicate n TCsort.vf).length)) :
          M.relMap (.vf r) (fun i => (hs i).symm ▸ S.join (x.1 i) (x.2 i)) ↔ M.relMap (.vf r) args := by
        exact (congrArg (M.relMap (.vf r)) (funext fun i => (empty i).elim)).to_iff
      by_cases h : M.relMap (.vf r) args
      · convert (SeparatedSets.univ (Set.definable_univ (A := A) (L := JG))
          (Set.definable_univ (A := B) (L := JH))) using 1
        ext x
        exact iff_of_true ((hEq x).mpr h) trivial
      · convert (SeparatedSets.empty (left := A.Definable JG) (right := B.Definable JH)) using 1
        ext x
        exact iff_of_false (h ∘ (hEq x).mp) id

omit D in
/-- A section that lifts an old value inside the old RV sort also keeps
the normalized residue of every old leading term in the old residue field. -/
theorem encode_mem_old_coordinates [L.Structure K]
    (C : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (hsection : ∀ t ∈ C.carrier .rv, S.representative (valueCoordinate t) ∈ C.carrier .rv)
    (t : C.carrier .rv) :
    (S.encode t.val).1 ∈ valueCoordinate '' C.carrier .rv ∧
      (S.encode t.val).2 ∈ residueRV O ⁻¹' C.carrier .rv := by
  refine ⟨⟨t.val, t.property, rfl⟩, ?_⟩
  let q := S.representative (valueCoordinate t.val)
  have hq : q ∈ C.carrier .rv := hsection t.val t.property
  have hinv : q⁻¹ ∈ C.carrier .rv := by
    let args : SortedArgs (CanonicalSort O) [.rv] := Fin.cases q (fun i => i.elim0)
    exact C.closed .rvInv args (fun i => by
      have h : i = 0 := Fin.fin_one_eq_zero i
      subst i
      exact hq)
  have hdiv : t.val / q ∈ C.carrier .rv := by
    rw [div_eq_mul_inv (G := RV0 O)]
    let args : SortedArgs (CanonicalSort O) [.rv, .rv] :=
      Fin.cases t.val (Fin.cases (q⁻¹ : RV0 O) (fun i => i.elim0))
    exact C.closed .rvMul args (fun i => by
      refine Fin.cases t.property (Fin.cases hinv (fun j => j.elim0)) i)
  have hm : t.val / q ∈ Set.range (residueRV O) := by
    rcases eq_or_ne t.val 0 with h | h
    · rw [h, zero_div (G₀ := RV0 O)]
      exact ⟨0, residueRV_zero O⟩
    · apply div_mem_residueRV_of_equal_unsignedValue O
      rw [show unsignedValue O q = valueCoordinate t.val from S.unsignedValue_representative _,
        coe_valueCoordinate h]
  change residueRV O (rvResidue O (t.val / q)) ∈ C.carrier .rv
  rwa [residueRV_rvResidue_of_mem_range O hm]

/-- An RV-definable unsigned-value pullback yields a definable set in
the value language over the old value parameters. The slice at residue
one selects a positive representative for every value. -/
theorem definable_value_set_of_rv_pullback [L.Structure K] {I : Type a} [Finite I]
    (g : E → PositiveField K →* PositiveField K)
    (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (hclamp : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
    (hsection : ∀ e γ, P e (S.representative γ) = S.representative (p e γ))
    (C : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (hparams : ∀ t : C.carrier .rv, (S.encode t.val).1 ∈ A ∧ (S.encode t.val).2 ∈ B)
    (hQE : ∀ φ : SortedFormula L E (FullRVVariables C I),
      ∃ q : SortedFormula L E (FullRVVariables C I), q.IsQF ∧
        ∀ v, q.realize (canonicalStructure (L := L) O hO P) v ↔
          φ.realize (canonicalStructure (L := L) O hO P) v)
    (U : Set (I → O.ValueGroupˣ))
    (hU : SortedDefinableOver (canonicalStructure (L := L) O hO P) C.carrier
      {x : ∀ s, RVVariables I s → CanonicalSort O s |
        (∀ i, x .rv i ≠ 0) ∧ (fun i => valueCoordinate (x .rv i)) ∈ U}) :
    A.Definable JG U := by
  let Q := S.canonicalCoordinatePresentation D g hP hclamp hunit hsection
  let pullback : Set (I → RV0 O) := {x | (∀ i, x i ≠ 0) ∧ (fun i => valueCoordinate (x i)) ∈ U}
  have hSplit := Q.separated_rv_pullback (U := pullback) C hU hQE hparams
    (S.separated_decoded_coordinate_graph D)
  have h := SeparatedSets.slice (Set.definable_empty (A := A) (L := JG)) (fun h₁ h₂ => h₁.union h₂)
    (fun _ : I => (1 : Residue O)) hSplit
  convert h using 1
  ext γ
  change γ ∈ U ↔
    (∀ i, S.join (γ i) 1 ≠ 0) ∧ (fun i => valueCoordinate (S.join (γ i) 1)) ∈ U
  have he : (fun i => valueCoordinate (S.join (γ i) 1)) = γ :=
    funext fun i => S.valueCoordinate_join (γ i) one_ne_zero
  rw [he]
  exact ⟨fun h => ⟨fun i => S.join_ne_zero (γ i) one_ne_zero, h⟩, And.right⟩

end RVValueSection

end GeneralizedEuler.Section2
