module

public import Section3.DiscParameters
public import Section3.UnaryDiscImages

public section

namespace GeneralizedEuler.Section3

open FirstOrder FirstOrder.Language GeneralizedEuler.Section2 Set

variable {K V W I : Type*} {L : Language} [L.Structure K]

/-- First-order definability with a fixed imaginary represented by the
class C. The same field formula must work for every tuple in the class. -/
def OverRepresentativeClass (P : Set K) (C : Set (I → K)) (A : Set (V → K)) : Prop :=
  ∃ φ : L.Formula ((P : Type _) ⊕ (V ⊕ I)), ∀ x c, c ∈ C →
    (x ∈ A ↔ φ.Realize (Sum.elim Subtype.val (Sum.elim x c)))

/-- For a named tuple of discs the equivalence test on field representatives
is a finite conjunction of the intrinsic disc-equality formulas of 2.32. -/
theorem disc_representative_class_formula [Field K] (O : ValuationSubring K)
    {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    {n : ℕ} (closed : Fin n → Bool) (D : Fin n → Set K) :
    let I := Fin n ⊕ Fin n
    let C := {c : I → K | ∀ i, D i = (if closed i then closedDisc else openDisc) O
      (c (.inl i)) (O.valuation (c (.inr i)))}
    letI := convexStructure O L
    ∃ eqn : (convexLanguage L).Formula (I ⊕ I), ∀ c ∈ C, ∀ d,
      eqn.Realize (Sum.elim c d) ↔ d ∈ C := by
  let := convexStructure O L
  let I := Fin n ⊕ Fin n
  let cmp (i : Fin n) : (convexLanguage L).Formula (I ⊕ I) :=
    discEqualFormula F (closed i) (closed i) (.var (.inl (.inl i))) (.var (.inl (.inr i)))
      (.var (.inr (.inl i))) (.var (.inr (.inr i)))
  refine ⟨Formula.iInf cmp,fun c hc d => ?_⟩
  rw [Formula.realize_iInf]
  apply forall_congr'
  intro i
  rw [hc i]
  exact realize_discEqualFormula O hF _ _ _ _ _ _ _

/-- Atomicity of a rectangular slice over its other coordinates and the
original imaginaries. Quantifying a fresh representative prevents the
lifted formula from depending on a choice of centers off the slice. -/
theorem atomic_slice_with_representatives [Finite I] (P : Set K) (C : Set (I → K)) (hc : C.Nonempty)
    (eqn : L.Formula (I ⊕ I)) (he : ∀ c ∈ C, ∀ d, eqn.Realize (Sum.elim c d) ↔ d ∈ C)
    {A : Set (V → K)} {B : Set (W → K)} {b : W → K} (hb : b ∈ B)
    (atom : AtomicOver (OverRepresentativeClass (L := L) P C)
      {u : V ⊕ W → K | u ∘ Sum.inl ∈ A ∧ u ∘ Sum.inr ∈ B}) :
    AtomicOver (OverRepresentativeClass (L := L) (P ∪ range b) C) A := by
  classical
  let Q := P ∪ range b
  obtain ⟨α,hα⟩ := atom.1
  let fix : P ⊕ ((V ⊕ W) ⊕ I) → (Q : Type _) ⊕ (V ⊕ I)
    | .inl p => .inl ⟨p.val,Or.inl p.property⟩
    | .inr (.inl (.inl j)) => .inr (.inl j)
    | .inr (.inl (.inr j)) => .inl ⟨b j,Or.inr (mem_range_self j)⟩
    | .inr (.inr j) => .inr (.inr j)
  refine ⟨⟨α.relabel fix,fun x c h => ?_⟩,?_,?_⟩
  · rw [Formula.realize_relabel]
    have v : Sum.elim Subtype.val (Sum.elim x c) ∘ fix =
      Sum.elim Subtype.val (Sum.elim (Sum.elim x b) c) := by funext z; rcases z with p | ((j|j)|j) <;> rfl
    rw [v,←hα _ _ h]
    exact (and_iff_left hb).symm
  · obtain ⟨u,hu,_⟩ := atom.2.nonempty
    exact ⟨u ∘ Sum.inl,hu⟩
  rintro D ⟨φ,hφ⟩
  let free (q : Q) : P ⊕ (V ⊕ W) :=
    if h : q.val ∈ P then .inl ⟨q.val,h⟩ else .inr (.inr ((q.property.resolve_left h).choose))
  let param (u : V ⊕ W → K) := Sum.elim Subtype.val u ∘ free
  have fixed (x : V → K) (q : Q) : param (Sum.elim x b) q = q.val := by
    simp only [param,Function.comp_apply,free]
    split
    · rfl
    · rename_i h
      exact (q.property.resolve_left h).choose_spec
  let lifted (u : V ⊕ W → K) := ∃ d ∈ C, φ.Realize (Sum.elim (param u) (Sum.elim (u ∘ Sum.inl) d))
  have defLift : OverRepresentativeClass (L := L) P C {u | lifted u} := by
    let H := (P : Type _) ⊕ ((V ⊕ W) ⊕ I)
    let ρ : Q ⊕ (V ⊕ I) → H ⊕ I
      | .inl q => .inl ((free q).map id Sum.inl)
      | .inr (.inl j) => .inl (.inr (.inl (.inl j)))
      | .inr (.inr j) => .inr j
    let pair : I ⊕ I → H ⊕ I := Sum.elim (fun j => .inl (.inr (.inr j))) Sum.inr
    refine ⟨Formula.iExs I (eqn.relabel pair ⊓ φ.relabel ρ),fun u c h => ?_⟩
    simp only [Formula.realize_iExs,Formula.realize_inf,Formula.realize_relabel]
    apply exists_congr
    intro d
    let v : H ⊕ I → K := Sum.elim (Sum.elim Subtype.val (Sum.elim u c)) d
    have hp : v ∘ pair = Sum.elim c d := by funext z; cases z <;> rfl
    have hr : v ∘ ρ = Sum.elim (param u) (Sum.elim (u ∘ Sum.inl) d) := by
      funext z
      rcases z with q | j | j
      · change v (.inl ((free q).map id Sum.inl)) = Sum.elim Subtype.val u (free q)
        cases free q <;> rfl
      · rfl
      · rfl
    change _ ↔ eqn.Realize (v ∘ pair) ∧ φ.Realize (v ∘ ρ)
    rw [hp,hr,he c h]
  have onSlice (x : V → K) : lifted (Sum.elim x b) ↔ x ∈ D := by
    have par : param (Sum.elim x b) = Subtype.val := funext (fixed x)
    change (∃ d ∈ C, φ.Realize (Sum.elim (param (Sum.elim x b)) (Sum.elim x d))) ↔ _
    rw [par]
    exact ⟨fun ⟨d,hd,hdx⟩ => (hφ x d hd).mpr hdx,
      fun hx => ⟨hc.choose,hc.choose_spec,(hφ x _ hc.choose_spec).mp hx⟩⟩
  intro x hx y hy
  exact (onSlice x).symm.trans ((atom.2.uniform _ defLift (Sum.elim x b) ⟨hx,hb⟩
    (Sum.elim y b) ⟨hy,hb⟩).trans (onSlice y))

theorem OverRepresentativeClass.pullback {P : Set K} {C : Set (I → K)} {A : Set (V → K)}
    (hd : OverRepresentativeClass (L := L) P C A) (j : V → W) :
    OverRepresentativeClass (L := L) P C {u | u ∘ j ∈ A} := by
  obtain ⟨φ,hφ⟩ := hd
  refine ⟨φ.relabel (Sum.map id (Sum.map j id)),fun u c hc => ?_⟩
  rw [Formula.realize_relabel]
  apply (hφ _ _ hc).trans
  apply Iff.of_eq
  congr 1
  funext z
  rcases z with p | j | i <;> rfl

theorem atomic_reindex_with_representatives {P : Set K} {C : Set (I → K)} {A : Set (V → K)}
    (atom : AtomicOver (OverRepresentativeClass (L := L) P C) A) (e : V ≃ W) :
    AtomicOver (OverRepresentativeClass (L := L) P C) {u : W → K | u ∘ e ∈ A} := by
  obtain ⟨x,hx⟩ := atom.2.nonempty
  refine ⟨atom.1.pullback e,⟨x ∘ e.symm,by simpa [Function.comp_assoc] using hx⟩,?_⟩
  intro B hB a ha b hb
  have h := atom.2.uniform _ (hB.pullback e.symm) (a ∘ e) ha (b ∘ e) hb
  simpa [Function.comp_assoc] using h

/-- In each coordinate the unary disc is atomic over every other fixed
coordinate and the original named disc codes. -/
theorem atomic_coordinate_with_representatives [Finite I] (P : Set K) (C : Set (I → K)) (hc : C.Nonempty)
    (eqn : L.Formula (I ⊕ I)) (he : ∀ c ∈ C, ∀ d, eqn.Realize (Sum.elim c d) ↔ d ∈ C)
    {n : ℕ} (D : Fin (n+1) → Set K)
    (atom : AtomicOver (OverRepresentativeClass (L := L) P C) {u | ∀ i, u i ∈ D i})
    (j : Fin (n+1)) (a : Fin (n+1) → K) (ha : ∀ i, a i ∈ D i) :
    AtomicOver (OverRepresentativeClass (L := L) (P ∪ range (j.removeNth a)) C)
      {u : Unit → K | u () ∈ D j} := by
  let e : Fin (n+1) ≃ Unit ⊕ Fin n :=
    { toFun := j.succAboveCases (.inl ()) Sum.inr
      invFun := Sum.elim (fun _ => j) j.succAbove
      left_inv := by
        intro k
        refine j.succAboveCases ?_ (fun m => ?_) k <;> simp
      right_inv := by rintro (⟨⟩|m) <;> simp }
  let B := {b : Fin n → K | ∀ k, b k ∈ D (j.succAbove k)}
  have hb : j.removeNth a ∈ B := fun k => ha (j.succAbove k)
  apply atomic_slice_with_representatives P C hc eqn he hb
  have h := atomic_reindex_with_representatives atom e
  convert h using 1
  ext u
  change (u (.inl ()) ∈ D j ∧ ∀ k, u (.inr k) ∈ D (j.succAbove k)) ↔ ∀ i, u (e i) ∈ D i
  constructor
  · rintro ⟨h₀,h₁⟩ k
    refine j.succAboveCases ?_ (fun i => ?_) k
    · simpa [e] using h₀
    · simpa [e] using h₁ i
  · intro h
    exact ⟨by simpa [e] using h j,fun i => by simpa [e] using h (j.succAbove i)⟩

end GeneralizedEuler.Section3
