module

public import Section3.SmallParameterGerms
public import Section3.DiscAtomicSlices
import all Section3.DiscAtomicSlices
import all Section2.ValuedFieldFormulas
import all Section2.WeakOminimal

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [Field K] [LinearOrder K] {L : Language} [L.Structure K]
    (O : ValuationSubring K) {V I : Type*} (P : Set K) (C : Set (I → K))

/-- Representatives of the old code and of one extra value. -/
def withValueRepresentatives (b : O.ValueGroup) : Set (I ⊕ Unit → K) :=
  {w | w ∘ Sum.inl ∈ C ∧ O.valuation (w (.inr ())) = b}

def withFieldRepresentatives (a : K) : Set (I ⊕ Unit → K) :=
  {w | w ∘ Sum.inl ∈ C ∧ w (.inr ()) = a}

/-- The bounded, two-sided germ predicate used for transfer in 3.18 is
definable over the old imaginary and the new value. This is uniform in
all representatives, including the representative of the bound. -/
theorem represented_bounded_germ {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (positive : (convexLanguage L).Formula Unit) (hp : letI := convexStructure O L;
      ∀ w : Unit → K, positive.Realize w ↔ 0 < w ())
    (Q : (V → K) → K → Prop) (b : O.ValueGroup) (p n : Prop) :
    letI := convexStructure O L
    OverRepresentativeClass (L := convexLanguage L) P C {u : V ⊕ Unit → K | Q (u ∘ Sum.inl) (u (.inr ()))} →
    OverRepresentativeClass (L := convexLanguage L) P (withValueRepresentatives O C b)
      {x | ∀ e, O.valuation e < b → e ≠ 0 → (Q x e ↔ if 0 < e then p else n)} := by
  let := convexStructure O L
  classical
  rintro ⟨φ,hφ⟩
  let J := convexLanguage L
  let N := P ⊕ (V ⊕ (I ⊕ Unit))
  let e : N ⊕ Unit := .inr ()
  let bound : N ⊕ Unit := .inl (.inr (.inr (.inr ())))
  let ρ : P ⊕ ((V ⊕ Unit) ⊕ I) → N ⊕ Unit := Sum.elim (Sum.inl ∘ Sum.inl)
    (Sum.elim (Sum.elim (fun j => .inl (.inr (.inl j))) (fun _ => e)) (fun j => .inl (.inr (.inr (.inl j)))))
  let truth (q : Prop) : J.Formula (N ⊕ Unit) := if q then ⊤ else ⊥
  let sign := positive.relabel (fun _ => e)
  let either := (sign.imp (truth p)) ⊓ (sign.not.imp (truth n))
  let small := (valuationLEFormula F (.var bound) (.var e)).not
  let nz := (Term.equal (.var e) (zeroTerm F)).not
  refine ⟨Formula.iAlls Unit (small.imp (nz.imp ((φ.relabel ρ).iff either))),fun x w hw => ?_⟩
  let v : N → K := Sum.elim Subtype.val (Sum.elim x w)
  have heval (z : Unit → K) : (φ.relabel ρ).Realize (Sum.elim v z) ↔ Q x (z ()) := by
    rw [Formula.realize_relabel]
    have assign : Sum.elim v z ∘ ρ = Sum.elim Subtype.val (Sum.elim (Sum.elim x z) (w ∘ Sum.inl)) := by
      funext j; rcases j with j | (j|j) | j <;> rfl
    rw [assign]; exact (hφ (Sum.elim x z) (w ∘ Sum.inl) hw.1).symm
  have tr (q : Prop) (z : Unit → K) : (truth q).Realize (Sum.elim v z) ↔ q := by by_cases h : q <;> simp [truth,h]
  have sg (z : Unit → K) : sign.Realize (Sum.elim v z) ↔ 0 < z () := by rw [Formula.realize_relabel]; exact hp _
  have val (z : Unit → K) : small.Realize (Sum.elim v z) ↔ O.valuation (z ()) < b := by
    rw [Formula.realize_not,realize_valuationLEFormula O hF,not_le]
    change O.valuation (z ()) < O.valuation (w (.inr ())) ↔ _
    rw [hw.2]
  have nonz (z : Unit → K) : nz.Realize (Sum.elim v z) ↔ z () ≠ 0 := by
    rw [Formula.realize_not,Formula.realize_equal,realize_zeroTerm O hF]; rfl
  change (∀ z, O.valuation z < b → z ≠ 0 → _) ↔ (Formula.iAlls Unit _).Realize v
  simp only [Formula.realize_iAlls,Formula.realize_imp,Formula.realize_iff,Formula.realize_inf,
    Formula.realize_not,either,val,nonz,heval,sg,tr]
  have split (z : K) : (if 0 < z then p else n) ↔ ((0 < z → p) ∧ (¬0 < z → n)) := by by_cases h : 0 < z <;> simp [h]
  exact ⟨fun h z l ne => (h (z ()) l ne).trans (split _),
    fun h z l ne => (h (fun _ => z) l ne).trans (split z).symm⟩

omit [Field K] [LinearOrder K] in
/-- Canonical interpretation of any formula over a code and one field
parameter. Quantifying equivalent old representatives makes the whole
family invariant even if the original formula defined a set only
for a particular specialization of the field parameter. -/
theorem uniform_parameter_tests [Finite I] (Cne : C.Nonempty) (eqn : L.Formula (I ⊕ I))
    (sameClass : ∀ c ∈ C, ∀ d, eqn.Realize (Sum.elim c d) ↔ d ∈ C) :
    ∃ Q : L.Formula (P ⊕ (V ⊕ (I ⊕ Unit))) → (V → K) → K → Prop,
      (∀ φ, OverRepresentativeClass (L := L) P C {u : V ⊕ Unit → K | Q φ (u ∘ Sum.inl) (u (.inr ()))}) ∧
      ∀ a B, OverRepresentativeClass (L := L) P (withFieldRepresentatives C a) B →
        ∃ φ, ∀ x, x ∈ B ↔ Q φ x a := by
  let N := P ⊕ ((V ⊕ Unit) ⊕ I)
  let Q (φ : L.Formula (P ⊕ (V ⊕ (I ⊕ Unit)))) (x : V → K) (a : K) :=
    ∃ d ∈ C, φ.Realize (Sum.elim Subtype.val (Sum.elim x (Sum.elim d (fun _ => a))))
  refine ⟨Q,fun φ => ?_,?_⟩
  · let pair : I ⊕ I → N ⊕ I := Sum.elim (fun j => .inl (.inr (.inr j))) Sum.inr
    let ρ : P ⊕ (V ⊕ (I ⊕ Unit)) → N ⊕ I := Sum.elim (Sum.inl ∘ Sum.inl)
      (Sum.elim (fun j => .inl (.inr (.inl (.inl j)))) (Sum.elim Sum.inr (fun _ => .inl (.inr (.inl (.inr ()))))))
    refine ⟨Formula.iExs I (eqn.relabel pair ⊓ φ.relabel ρ),fun u c hc => ?_⟩
    simp only [Formula.realize_iExs,Formula.realize_inf,Formula.realize_relabel]
    apply exists_congr; intro d
    have e1 : Sum.elim (Sum.elim Subtype.val (Sum.elim u c)) d ∘ pair = Sum.elim c d := by funext j; cases j <;> rfl
    have e2 : Sum.elim (Sum.elim Subtype.val (Sum.elim u c)) d ∘ ρ =
        Sum.elim Subtype.val (Sum.elim (u ∘ Sum.inl) (Sum.elim d (fun _ : Unit => u (.inr ())))) := by
      funext j; rcases j with j | j | (j|j) <;> rfl
    rw [e1,e2,sameClass c hc d]
  · rintro a B ⟨φ,hφ⟩
    refine ⟨φ,fun x => ?_⟩
    have test (d : I → K) (hd : d ∈ C) := hφ x (Sum.elim d (fun _ => a)) (show Sum.elim d (fun _ : Unit => a) ∈ withFieldRepresentatives C a from ⟨hd,rfl⟩)
    exact ⟨fun h => ⟨Cne.choose,Cne.choose_spec,(test _ Cne.choose_spec).mp h⟩,fun ⟨d,hd,h⟩ => (test d hd).mpr h⟩

variable [IsStrictOrderedRing K]

/-- Lemma 3.18 for an actual family of disc-code representatives.
The code equivalence is given by the disc-equality formula of 2.32,
and the value-atomicity hypothesis is precisely 3.12 over that code.
The cutoff is independent of the new field parameter and its sign. -/
theorem atomic_over_every_small_represented_parameter [Finite I] [DenselyOrdered O.ValueGroup]
    (hO : IsOrderConvex O) (Cne : C.Nonempty) (A : Set (V → K)) (ne : A.Nonempty)
    (F : FieldTerms (convexLanguage L)) (positive : (convexLanguage L).Formula Unit)
    (eqn : (convexLanguage L).Formula (I ⊕ I)) :
    letI := convexStructure O L
    InterpretsFieldTerms (K := K) F → (∀ w : Unit → K, positive.Realize w ↔ 0 < w ()) →
    (∀ c ∈ C, ∀ d, eqn.Realize (Sum.elim c d) ↔ d ∈ C) →
    (∀ D : Set K, (univ : Set K).Definable₁ (convexLanguage L) D → FiniteConvexUnion D) →
    RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K (Option ((convexLanguage L).Formula (P ⊕ (V ⊕ (I ⊕ Unit))))) →
    OverRepresentativeClass (L := convexLanguage L) P C A →
    (∀ b, AtomicOver (OverRepresentativeClass (L := convexLanguage L) P (withValueRepresentatives O C b)) A) →
    ∃ β : O.ValueGroup, 0 < β ∧ ∀ e, O.valuation e < β → e ≠ 0 →
      AtomicOver (OverRepresentativeClass (L := convexLanguage L) P (withFieldRepresentatives C e)) A := by
  let := convexStructure O L
  let J := convexLanguage L
  intro hF hp sameClass weak sat dA atom
  obtain ⟨Q,dQ,hQ⟩ := uniform_parameter_tests P C Cne eqn sameClass (V := V)
  have named (e : K) : OverRepresentativeClass (L := J) P (withFieldRepresentatives C e) A := by
    obtain ⟨φ,hφ⟩ := dA
    let ρ : P ⊕ (V ⊕ I) → P ⊕ (V ⊕ (I ⊕ Unit)) := Sum.map id (Sum.map id Sum.inl)
    refine ⟨φ.relabel ρ,fun x w hw => ?_⟩
    rw [Formula.realize_relabel]
    have he : Sum.elim Subtype.val (Sum.elim x w) ∘ ρ = Sum.elim Subtype.val (Sum.elim x (w ∘ Sum.inl)) := by
      funext j; rcases j with j|j|j <;> rfl
    rw [he]; exact hφ _ _ hw.1
  apply saturated_small_parameter_atomicity O F hF sat hO A ne Q _ _ atom
    (fun i b p n => represented_bounded_germ O P C hF positive hp (Q i) b p n (dQ i)) _ named
    (fun e B hB => (hQ e B hB).imp (fun i hi x _ => hi x))
  intro i x _ side w
  obtain ⟨φ,hφ⟩ := dQ i
  let c := Cne.choose
  let D := {y : K | Q i x y}
  have defD : (univ : Set K).Definable₁ J D := by
    let idx : K → (univ : Set K) := fun a => ⟨a,mem_univ a⟩
    let ρ : P ⊕ ((V ⊕ Unit) ⊕ I) → (univ : Set K) ⊕ Fin 1 :=
      Sum.elim (fun p => .inl (idx p.val)) (Sum.elim (Sum.elim (fun j => .inl (idx (x j))) (fun _ => .inr 0)) (fun j => .inl (idx (c j))))
    apply definable_iff_exists_formula_sum.mpr
    refine ⟨φ.relabel ρ,?_⟩
    ext t
    change Q i x (t 0) ↔ (φ.relabel ρ).Realize (Sum.elim Subtype.val t)
    rw [Formula.realize_relabel]
    have he : Sum.elim Subtype.val t ∘ ρ = Sum.elim Subtype.val (Sum.elim (Sum.elim x (fun _ : Unit => t 0)) c) := by
      funext j; rcases j with j | (j|j) | j <;> rfl
    rw [he]; exact hφ (Sum.elim x (fun _ => t 0)) c Cne.choose_spec
  let B := {t : K | Q i x t ↔ w = true}
  have db : (univ : Set K).Definable₁ J B := by
    cases w <;> simp only [B,Bool.false_eq_true,iff_false,iff_true]
    · exact defD.compl
    · exact defD
  obtain ⟨m,U,cv,eqB⟩ := weak B db
  let reflect (t : K) := if side then -t else t
  let T (j : Fin m) := Ioo 0 1 ∩ reflect ⁻¹' U j
  refine ⟨m,T,fun j => Set.OrdConnected.inter inferInstance ?_,?_⟩
  · cases side
    · exact cv j
    · exact (cv j).preimage_anti (fun a b h => neg_le_neg h)
  · ext t
    change (t ∈ Ioo 0 1 ∧ reflect t ∈ B) ↔ _
    rw [eqB]
    simp [T]

end GeneralizedEuler.Section3
