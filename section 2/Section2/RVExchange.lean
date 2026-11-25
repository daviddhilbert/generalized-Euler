module

public import Section2.RVClosure
public import Section2.RVMonomials
public import Section2.RVAgreement
public import Section2.FieldDefinableClosure

/-! The term-level exchange calculations of Remark 2.27. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w z

variable {L : Language.{u, v}} {E : Type w}
  {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

/-- A point evaluated by an RV term over the parameters is definable
over those same parameters. -/
theorem definable_rv_point_of_term (W : Set (RV0 O)) {t : RV0 O}
    (term : SortedTerm L E (RVVariables W) .rv)
    (h : term.realize (canonicalStructure O hO P) (rvTermAssignment (Z := CanonicalSort O) Subtype.val) = t) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P)
      (fun s => match s with | .vf => ∅ | .rv => W)
      {a : ∀ s, RVVariables Unit s → CanonicalSort O s | a .rv () = t} := by
  let M := canonicalStructure (L := L) O hO P
  let A : ∀ s, Set (CanonicalSort O s)
    | .vf => ∅
    | .rv => W
  let v : ∀ s, RVVariables W s → (A s : Type z) ⊕ RVVariables Unit s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  refine ⟨.equal (.var (.inr ())) (term.relabel v), ?_⟩
  intro x
  have he : (fun s => Sum.elim Subtype.val (x s) ∘ v s) =
      rvTermAssignment (Z := CanonicalSort O) Subtype.val := by
    funext s i
    cases s
    · exact i.elim
    · rfl
  change x .rv () = t ↔ x .rv () =
    (term.relabel v).realize M (fun s => Sum.elim Subtype.val (x s))
  rw [SortedTerm.realize_relabel, he, h]

variable [Field E]
  (g : E → PositiveField K →* PositiveField K)
  (hP : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (hzero : ∀ x, g 0 x = 1) (hone : ∀ x, g 1 x = x)
  (hadd : ∀ e d x, g (e + d) x = g e x * g d x)
  (hmul : ∀ e d x, g (e * d) x = g e (g d x))

include hP hzero hone hadd hmul in
/-- A new monomial defines the positive generator over the old RV base. -/
theorem definable_rv_exchange_of_monomial (W : Set (RV0 O)) {t u x : RV0 O}
    (ht : IsPositiveRV O t) (hu : u ∈ W) (hu0 : u ≠ 0) {e : E} (he : e ≠ 0)
    (hx : x = u * P e t) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P)
      (fun s => match s with | .vf => ∅ | .rv => insert x W)
      {a : ∀ s, RVVariables Unit s → CanonicalSort O s | a .rv () = t} := by
  let a : (insert x W : Set (RV0 O)) := ⟨x, Set.mem_insert _ _⟩
  let c : (insert x W : Set (RV0 O)) := ⟨u, Set.mem_insert_of_mem _ hu⟩
  apply definable_rv_point_of_term O hO P (insert x W) (rvPowerTerm e⁻¹ (rvDivTerm (.var a) (.var c)))
  rw [realize_rvPowerTerm, realize_rvDivTerm]
  exact recover_rv_of_monomial O g P hP hzero hone hadd hmul ht hu0 he hx

omit [Field E] in
/-- At an old value, normalize both leading terms by old factors.
Exchange in the residue pregeometry supplies a residue term, and
substituting the normalized new point recovers the generator in RV. -/
theorem definable_rv_exchange_of_residue {T : L.Theory} [T.IsUniversal] [Residue O ⊨ T]
    (hQE : EliminatesQuantifiers T)
    (W : Set (RV0 O)) (hMul : ∀ c ∈ W, ∀ d ∈ W, c * d ∈ W)
    {t x u c : RV0 O} (hu : u ∈ W) (hc : c ∈ W) (hu0 : u ≠ 0) (hx : x ∉ W)
    (r q : Residue O) (ht : t = c * residueRV O r) (hq : x = u * residueRV O q)
    (old : Set (Residue O)) (hold : ∀ s, s ∈ old ↔ residueRV O s ∈ W)
    (B : Matroid (Residue O)) (hLoops : B.closure ∅ ⊆ old)
    (hNew : q ∈ B.closure {r})
    (hClosure : ∀ z y, y ∈ B.closure {z} → ∃ φ : L.Formula ((old ⊕ Unit) ⊕ Unit),
      ∀ s : Residue O, φ.Realize (Sum.elim (Sum.elim Subtype.val (fun _ => z)) (fun _ => s)) ↔ s = y) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P)
      (fun s => match s with | .vf => ∅ | .rv => insert x W)
      {a : ∀ s, RVVariables Unit s → CanonicalSort O s | a .rv () = t} := by
  have hqNew : residueRV O q ∉ W := by
    intro h
    exact hx (hq ▸ hMul u hu _ h)
  have hqLoop : q ∉ B.closure ∅ := fun h => hqNew ((hold q).mp (hLoops h))
  have hs (x : Residue O) : insert x ∅ = ({x} : Set (Residue O)) := by
    ext y
    simp
  have hNew' : q ∈ B.closure (insert r ∅) := by rwa [hs]
  have hExchange := B.closure_exchange (X := ∅) (f := r) (e := q) ⟨hNew', hqLoop⟩
  have hIn : r ∈ B.closure {q} := by simpa only [hs] using hExchange.1
  obtain ⟨φ, hφ⟩ := hClosure q r hIn
  obtain ⟨τ, hτ⟩ := exists_term_of_uniquely_definable hQE
    (Sum.elim Subtype.val (fun _ : Unit => q)) r φ hφ
  let V := RVVariables (insert x W : Set (RV0 O))
  let trim : SortedTerm L E V .rv :=
    rvDivTerm (.var ⟨x, Set.mem_insert _ _⟩) (.var ⟨u, Set.mem_insert_of_mem _ hu⟩)
  let args : ∀ s, RVVariables (old ⊕ Unit) s → SortedTerm L E V s
    | .vf => PEmpty.elim
    | .rv => Sum.elim
      (fun r => .var ⟨residueRV O r.val, Set.mem_insert_of_mem _ ((hold _).mp r.property)⟩)
      (fun _ => trim)
  let factor : SortedTerm L E V .rv := .var ⟨c, Set.mem_insert_of_mem _ hc⟩
  let term := rvMulTerm factor ((liftResidueTerm τ).subst args)
  let M := canonicalStructure (L := L) O hO P
  let v := rvTermAssignment (Z := CanonicalSort O) (fun a : ↥(insert x W : Set (RV0 O)) => a.val)
  have hTrim : trim.realize M v = residueRV O q := by
    dsimp only [trim]
    rw [realize_rvDivTerm]
    change x / u = residueRV O q
    rw [hq, mul_comm (G := RV0 O) u, div_eq_mul_inv (G := RV0 O), mul_assoc (G := RV0 O),
      mul_inv_cancel₀ (G₀ := RV0 O) hu0, mul_one (M := RV0 O)]
  have hV : (fun s i => (args s i).realize M v) =
      rvTermAssignment (Z := CanonicalSort O) (residueRV O ∘ Sum.elim Subtype.val (fun _ : Unit => q)) := by
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => cases i with
      | inl r => rfl
      | inr i => exact hTrim
  apply definable_rv_point_of_term O hO P (insert x W) term
  dsimp only [term]
  rw [realize_rvMulTerm, SortedTerm.realize_subst, hV, realize_liftResidueTerm, hτ]
  exact ht.symm

end GeneralizedEuler.Section2
