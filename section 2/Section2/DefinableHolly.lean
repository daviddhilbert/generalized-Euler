module

public import Section2.HollyNormalForm
public import Section2.QuotientInterpretation

/-! Definability of the components of a unary Holly normal form. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w u' v' z

/-- The one-variable family for the VF sort. -/
abbrev UnaryVFVariables : TCsort → Type
  | .vf => Fin 1
  | .rv => Empty

/-- Restricting the representative interpretation to one VF coordinate
gives definability in the valued-field language. -/
theorem definable₁_of_sorted_vf_definability
    {L : Language.{u, v}} {E : Type w} {J : Language.{u', v'}} {K : Type z} [Field K] [J.Structure K]
    (O : ValuationSubring K) {M : SortedStructure L E (CanonicalSort O)}
    {I : QuotientInterpretation J L E} (R : RealizesQuotientInterpretation I (A := K) M)
    (hVF : ∀ x, R.rep .vf x = x) {U : Set K} {A : ∀ s, Set (CanonicalSort O s)}
    (hU : SortedDefinableOver M A {a : ∀ s, UnaryVFVariables s → CanonicalSort O s | a .vf 0 ∈ U}) :
    (Set.univ : Set K).Definable₁ J U := by
  let coord : TaggedVar UnaryVFVariables → Fin 1 := fun
    | ⟨.vf, i⟩ => i
    | ⟨.rv, i⟩ => i.elim
  have h := Set.Definable.preimage_comp coord (R.definable_preimage_with_all_parameters hU)
  change (Set.univ : Set K).Definable J {x : Fin 1 → K | x 0 ∈ U}
  convert h using 1
  ext a
  change a 0 ∈ U ↔ R.assignment (a ∘ coord) .vf 0 ∈ U
  rw [RealizesQuotientInterpretation.assignment_apply, hVF]
  rfl

/-- Naming a point of a unary definable set makes its order-connected
component definable by the condition that the intervening interval lies
in the set. -/
theorem definable₁_ordConnectedComponent
    {J : Language.{u', v'}} {K : Type z} [LinearOrder K] [J.Structure K]
    (leSymbol : J.Relations 2) (hLE : ∀ v : Fin 2 → K, Structure.RelMap leSymbol v ↔ v 0 ≤ v 1)
    {A U : Set K} (hU : A.Definable₁ J U) (a : A) : A.Definable₁ J (Set.ordConnectedComponent U a.val) := by
  change A.Definable J {x : Fin 1 → K | x 0 ∈ U} at hU
  change A.Definable J {x : Fin 1 → K | x 0 ∈ Set.ordConnectedComponent U a.val}
  obtain ⟨φ, hφ⟩ := hU
  let order := (J.lhomWithConstants A).onRelation leSymbol
  let cmp (x y : (J[[A]]).Term (Fin 1 ⊕ Unit)) : (J[[A]]).Formula (Fin 1 ⊕ Unit) :=
    order.formula (Fin.cases x (fun _ => y))
  let x : (J[[A]]).Term (Fin 1 ⊕ Unit) := .var (.inl 0)
  let z : (J[[A]]).Term (Fin 1 ⊕ Unit) := .var (.inr ())
  let c : (J[[A]]).Term (Fin 1 ⊕ Unit) := (J.con a).term
  let between := (cmp c z ⊓ cmp z x) ⊔ (cmp x z ⊓ cmp z c)
  refine ⟨Formula.iAlls Unit (between.imp (φ.relabel (fun _ => .inr ()))), ?_⟩
  ext v
  have eval (s t : (J[[A]]).Term (Fin 1 ⊕ Unit)) (q : (Fin 1 ⊕ Unit) → K) :
      (cmp s t).Realize q ↔ s.realize q ≤ t.realize q := by
    change (order.formula (Fin.cases s (fun _ => t))).Realize q ↔ _
    rw [Formula.realize_rel, LHom.map_onRelation (J.lhomWithConstants A), hLE]
    rfl
  have evalBetween (r : Unit → K) : between.Realize (Sum.elim v r) ↔ r () ∈ Set.uIcc a.val (v 0) := by
    simp only [between, Formula.realize_sup, Formula.realize_inf, eval, c, z, x,
      Term.realize_con, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    constructor
    · exact fun h => h.elim (fun h₁ => Set.mem_uIcc_of_le h₁.1 h₁.2)
        (fun h₁ => Set.mem_uIcc_of_ge h₁.1 h₁.2)
    · intro h
      rcases le_total a.val (v 0) with hle | hge
      · rw [Set.uIcc_of_le hle] at h
        exact Or.inl h
      · rw [Set.uIcc_of_ge hge] at h
        exact Or.inr h
  change v 0 ∈ Set.ordConnectedComponent U a.val ↔
    (Formula.iAlls Unit (between.imp (φ.relabel (fun _ => .inr ())))).Realize v
  rw [Set.mem_ordConnectedComponent, Formula.realize_iAlls]
  simp only [Formula.realize_imp, evalBetween, Formula.realize_relabel]
  have evalU (r : Unit → K) : φ.Realize (Sum.elim v r ∘ (fun _ => .inr ())) ↔ r () ∈ U :=
    (Set.ext_iff.mp hφ (fun _ : Fin 1 => r ())).symm
  constructor
  · intro h r hr
    exact (evalU r).mpr (h hr)
  · intro h y hy
    exact (evalU (fun _ => y)).mp (h _ hy)

/-- Transfer to VF, apply the unary valuation description, and recover
the definable components of the unique Holly decomposition. -/
theorem exists_definable_holly_decomposition
    {L : Language.{u, v}} {E : Type w} {J : Language.{u', v'}}
    {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [J.Structure K]
    (O : ValuationSubring K) (hO : IsOrderConvex O) {M : SortedStructure L E (CanonicalSort O)}
    {I : QuotientInterpretation J L E} (R : RealizesQuotientInterpretation I (A := K) M)
    (hVF : ∀ x, R.rep .vf x = x) (leSymbol : J.Relations 2)
    (hLE : ∀ v : Fin 2 → K, Structure.RelMap leSymbol v ↔ v 0 ≤ v 1)
    (hBoolean : ∀ S : Set K, (Set.univ : Set K).Definable₁ J S → UnaryValuativeSet O S)
    {U : Set K} {A : ∀ s, Set (CanonicalSort O s)}
    (hU : SortedDefinableOver M A {a : ∀ s, UnaryVFVariables s → CanonicalSort O s | a .vf 0 ∈ U}) :
    ∃! pieces : Finset (Set K), IsHollyDecomposition O U pieces ∧
      ∀ C ∈ pieces, (Set.univ : Set K).Definable₁ J C := by
  have hd := definable₁_of_sorted_vf_definability O R hVF hU
  obtain ⟨pieces, hp, huniq⟩ := existsUnique_hollyDecomposition O hO (hBoolean U hd)
  refine ⟨pieces, ⟨hp, ?_⟩, fun _ h => huniq _ h.1⟩
  intro C hC
  obtain ⟨a, ha⟩ := (hp.1 C hC).1
  rw [hp.piece_eq_component O hC ha]
  exact definable₁_ordConnectedComponent leSymbol hLE hd ⟨a, Set.mem_univ a⟩

end GeneralizedEuler.Section2
