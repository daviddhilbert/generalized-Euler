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

section NewValue

variable (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
  (hunit : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)

include hP hone hmul hunit in
/-- At a new value, a monomial can be a residue only if its exponent
is zero. Applying the inverse power would otherwise produce an old
representative of the new value. -/
theorem exponent_eq_zero_of_new_value_of_substructure
    (minusIn : rv O (-1) ∈ S.carrier .rv) {t : RV0 O} (ht : IsPositiveRV O t)
    (hNew : unsignedValue O t ∉ unsignedValue O '' S.carrier .rv)
    (u : RV0 O) (hu : u ∈ S.carrier .rv) (hu0 : u ≠ 0) (e : E)
    (h : unsignedValue O (u * P e t) = 1) : e = 0 := by
  by_contra he
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨c, rfl⟩ := rv_surjective O u
  have hc0 : c ≠ 0 := (rv_eq_zero_iff O).not.mp hu0
  let r : PositiveField K := ⟨|c|, abs_pos.mpr hc0⟩
  have hr : rv O r.val ∈ S.carrier .rv := by
    change rv O |c| ∈ S.carrier .rv
    rcases le_or_gt 0 c with hc | hc
    · rw [abs_of_nonneg hc]
      exact hu
    · rw [abs_of_neg hc, ← neg_one_mul c, map_mul]
      let args : SortedArgs (CanonicalSort O) [.rv, .rv] :=
        Fin.cases (rv O (-1)) (Fin.cases (rv O c) (fun i => i.elim0))
      exact S.closed .rvMul args
        (fun i => Fin.cases minusIn (Fin.cases hu (fun j => j.elim0)) i)
  have hInv : rv O (r⁻¹ : PositiveField K).val ∈ S.carrier .rv := by
    rw [Positive.coe_inv, map_inv₀]
    let args : SortedArgs (CanonicalSort O) [.rv] := Fin.cases (rv O r.val) (fun i => i.elim0)
    exact S.closed .rvInv args (fun i => Fin.cases hr (fun j => j.elim0) i)
  rw [hP e a, ← map_mul (rv O), unsignedValue_rv, map_mul O.valuation] at h
  have hVal : O.valuation (g e a : K) = O.valuation (r⁻¹ : PositiveField K).val := by
    rw [Positive.coe_inv, map_inv₀]
    change O.valuation (g e a : K) = (O.valuation |c|)⁻¹
    rw [valuation_abs]
    apply (mul_eq_one_iff_eq_inv₀ ((map_ne_zero O.valuation).mpr hc0)).mp
    rw [mul_comm]
    exact h
  have hv := power_respects_unsignedValue O (g e⁻¹) (hunit e⁻¹) hVal
  rw [← hmul, inv_mul_cancel₀ he, hone] at hv
  let s := rv O (r⁻¹ : PositiveField K).val
  have hPold : P e⁻¹ s ∈ S.carrier .rv := by
    let args : SortedArgs (CanonicalSort O) [.rv] := Fin.cases s (fun i => i.elim0)
    exact S.closed (.power e⁻¹) args (fun i => Fin.cases hInv (fun j => j.elim0) i)
  refine hNew ⟨P e⁻¹ s, hPold, ?_⟩
  change unsignedValue O (P e⁻¹ (rv O (r⁻¹ : PositiveField K).val)) = unsignedValue O (rv O a.val)
  rw [hP, unsignedValue_rv, unsignedValue_rv]
  exact hv.symm

include hP hzero hone hadd hmul hunit in
/-- At a new value, definable closure puts a point defined from the
generator in the checked monomial extension of the old RV base. -/
theorem definable_rv_exchange_at_new_value
    (minusIn : rv O (-1) ∈ S.carrier .rv)
    (hOff : ∀ e t, ¬IsPositiveRV O t → P e t = 0)
    (hDcl : ∀ C : SortedSubstructure (canonicalStructure (L := L) O hO P),
      RVDefinablyClosed (canonicalStructure (L := L) O hO P) (C.carrier .rv))
    {t x : RV0 O}
    (hVal : unsignedValue O t ∉ unsignedValue O '' S.carrier .rv)
    (hNew : x ∉ S.carrier .rv)
    (hDef : SortedDefinableOver (canonicalStructure (L := L) O hO P)
      (fun s => match s with | .vf => ∅ | .rv => insert t (S.carrier .rv))
      {a : ∀ s, RVVariables Unit s → CanonicalSort O s | a .rv () = x}) :
    SortedDefinableOver (canonicalStructure (L := L) O hO P)
      (fun s => match s with | .vf => ∅ | .rv => insert x (S.carrier .rv))
      {a : ∀ s, RVVariables Unit s → CanonicalSort O s | a .rv () = t} := by
  obtain ⟨a, rfl⟩ := rv_surjective O t
  let V := S.carrier .rv
  have h0 : (0 : RV0 O) ∈ V := S.closed .rvZero (fun i => i.elim0) (fun i => i.elim0)
  have h1 : (1 : RV0 O) ∈ V := S.closed .rvOne (fun i => i.elim0) (fun i => i.elim0)
  have ha : a ≠ 0 := by
    intro he
    exact hVal ⟨0, h0, by simp [he]⟩
  let t := rv O |a|
  let factor : RV0 O := if a < 0 then rv O (-1) else 1
  have hFactor : factor ∈ V ∧ factor ≠ 0 ∧ rv O a = factor * t := by
    by_cases hn : a < 0
    · refine ⟨by simpa [factor, hn] using minusIn, ?_, ?_⟩
      · simp [factor, hn, rv_eq_zero_iff]
      · simp only [factor, hn, ↓reduceIte, t, abs_of_neg hn, ← map_mul (rv O),
          neg_one_mul, neg_neg]
    · simp only [factor, hn, ↓reduceIte, t, abs_of_nonneg (le_of_not_gt hn), one_mul (M := RV0 O)]
      exact ⟨h1, IsPositiveRV.ne_zero O (isPositiveRV_one O), trivial⟩
  have ht : IsPositiveRV O t := ⟨⟨|a|, abs_pos.mpr ha⟩, rfl⟩
  have htVal : unsignedValue O t ∉ unsignedValue O '' V := by
    simpa only [t, unsignedValue_rv, valuation_abs] using hVal
  have hExponent := exponent_eq_zero_of_new_value_of_substructure O hO P g hP hone hmul S hunit
    minusIn ht htVal
  let C := adjoinNewValueRV O g P hP hzero hone hadd hmul hO hOff S t ht hExponent
  have hCarrier : C.carrier .rv = rvOneGeneratorMonomials O P V t :=
    adjoinNewValueRV_rv_carrier O g P hP hzero hone hadd hmul hO hOff S t ht hExponent
  have hL := leadingTermPower_scalarLaws O hP hzero hone hadd hmul ht
  have htC : rv O a ∈ C.carrier .rv := by
    rw [hCarrier]
    exact Or.inr ⟨factor, hFactor.1, hFactor.2.1, 1, by rw [hL.2.1, hFactor.2.2]⟩
  have hxC : x ∈ C.carrier .rv := hDcl C x (hDef.mono (fun s => by
    cases s with
    | vf => exact Set.Subset.rfl
    | rv =>
      intro u hu
      rcases hu with rfl | hu
      · exact htC
      · rw [hCarrier]
        by_cases h : u = 0
        · exact Or.inl h
        · exact Or.inr ⟨u, hu, h, 0, by rw [hL.1, mul_one (M := RV0 O)]⟩))
  rw [hCarrier] at hxC
  have hx0 : x ≠ 0 := fun he => hNew (he.symm ▸ h0)
  obtain ⟨u, hu, hu0, e, hx⟩ := hxC.resolve_left hx0
  have he : e ≠ 0 := fun he => hNew (by rwa [hx, he, hL.1, mul_one (M := RV0 O)])
  let W := insert x V
  let aVar : SortedTerm L E (RVVariables W) .rv := .var ⟨x, Set.mem_insert _ _⟩
  let uVar : SortedTerm L E (RVVariables W) .rv := .var ⟨u, Set.mem_insert_of_mem _ hu⟩
  let fVar : SortedTerm L E (RVVariables W) .rv := .var ⟨factor, Set.mem_insert_of_mem _ hFactor.1⟩
  let term := rvMulTerm fVar (rvPowerTerm e⁻¹ (rvDivTerm aVar uVar))
  apply definable_rv_point_of_term O hO P W term
  dsimp only [term]
  rw [realize_rvMulTerm, realize_rvPowerTerm, realize_rvDivTerm]
  change factor * P e⁻¹ (x / u) = rv O a
  rw [recover_rv_of_monomial O g P hP hzero hone hadd hmul ht hu0 he hx, ← hFactor.2.2]

end NewValue

end GeneralizedEuler.Section2
