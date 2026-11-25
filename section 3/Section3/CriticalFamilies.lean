module

public import Section3.PiecewiseFunctions
public import Section3.DerivativeFormula
import all Section3.DerivativeFormula
import all Section2.ContinuousDefinitions
import all Section3.DefinableFunctions

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set Filter
open scoped Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K]
    {L : Language} [L.Structure K] {P : Set K} {I : Type*} (F : OrderedFieldTerms L)
    (hF : InterpretsOrderedFieldTerms (A := K) F)

private theorem eventually_order_ball (x : K) (Q : K → Prop) :
    (∀ᶠ z in 𝓝 x, Q z) ↔ ∃ d > 0, ∀ z, |z-x| < d → Q z := by
  constructor
  · intro h
    obtain ⟨a,b,⟨ax,xb⟩,sub⟩ := mem_nhds_iff_exists_Ioo_subset.mp h
    refine ⟨min (x-a) (b-x),lt_min (sub_pos.mpr ax) (sub_pos.mpr xb),fun z hz => sub ?_⟩
    rcases lt_min_iff.mp hz with ⟨l,r⟩
    exact ⟨by linarith [(abs_lt.mp l).1],by linarith [(abs_lt.mp r).2]⟩
  · rintro ⟨d,hd,rule⟩
    filter_upwards [Ioo_mem_nhds (sub_lt_self x hd) (lt_add_of_pos_right x hd)] with z hz
    exact rule z (abs_lt.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩)

private theorem continuousAt_order_ball (g : K → K) (x : K) : ContinuousAt g x ↔
    ∀ e > 0, ∀ᶠ y in 𝓝 x, |g y-g x| < e := by
  constructor
  · intro cont e pos
    exact cont.tendsto.eventually ((eventually_order_ball _ _).mpr ⟨e,pos,fun _ h => h⟩)
  · intro cond
    apply Filter.tendsto_def.mpr
    intro S hs
    obtain ⟨e,ep,h⟩ := (eventually_order_ball _ _).mp hs
    exact (cond e ep).mono fun z hz => h _ hz

include hF in
/-- The unary germ of a definable family, at one of its named
coordinates. All quantifiers stay in the original ordered field. -/
theorem definable_fiber_germ (i : I) (Q : (I → K) → K → Prop)
    (dQ : P.Definable L {w : I ⊕ Unit → K | Q (w ∘ Sum.inl) (w (.inr ()))}) :
    P.Definable L {a | ∀ᶠ z in 𝓝 (a i), Q a z} := by
  let B := I ⊕ Unit
  let C := B ⊕ Unit
  let x : C := .inl (.inl i)
  let d : C := .inl (.inr ())
  let z : C := .inr ()
  let ρ : B → C := Sum.elim (Sum.inl ∘ Sum.inl) (fun _ => z)
  have near : P.Definable L {w : C → K | |w z-w x| < w d} :=
    definable_within F hF (DefinableFun.proj L) (DefinableFun.proj L) (DefinableFun.proj L)
  have impl : P.Definable L {w : C → K | |w z-w x| < w d → Q (w ∘ Sum.inl ∘ Sum.inl) (w z)} := by
    convert near.compl.union (dQ.preimage_comp ρ) using 1
    ext w; exact imp_iff_not_or
  let test (a : I → K) (d : K) := ∀ z, |z-a i| < d → Q a z
  have allZ : P.Definable L {w : B → K | test (w ∘ Sum.inl) (w (.inr ()))} := definable_forall_scalar impl
  have h := definable_positive_quantifier F hF (Q := test) allZ false
  convert h using 1
  ext a; exact eventually_order_ball (a i) (Q a)

include hF in
/-- The critical family in Lemma 3.3 is definable uniformly in every
field input. The formula describes discontinuity and the frontier of
the zero set on the varying one-dimensional section. -/
theorem definable_term_critical_family (t : L.Term (Option I)) :
    P.Definable L {w : Option I → K | w none ∈ criticalSet (fun y => t.realize (Option.elim · y (w ∘ some)))} := by
  let g (a : I → K) (y : K) := t.realize (Option.elim · y a)
  let U := Option I
  let B := U ⊕ Unit
  let W := B ⊕ Unit
  let pars (i : I) : W := .inl (.inl (some i))
  let x : W := .inl (.inl none)
  let z : W := .inr ()
  let eps : W := .inl (.inr ())
  have atTerm (v : W) : P.DefinableFun L (fun w : W → K => g (w ∘ pars) (w v)) := by
    let ρ : U → W := (Option.elim · v pars)
    convert (t.relabel ρ).definableFun_realize.of_empty using 1
    funext w; rw [Term.realize_relabel]; unfold g; apply congrArg t.realize; funext j; cases j <;> rfl
  let test (v : B → K) (y : K) := |g ((v ∘ Sum.inl) ∘ some) y - g ((v ∘ Sum.inl) ∘ some) (v (.inl none))| < v (.inr ())
  have close : P.Definable L {w : W → K | test (w ∘ Sum.inl) (w z)} :=
    definable_within F hF (atTerm z) (atTerm x) (DefinableFun.proj L)
  let cont (v : U → K) := ContinuousAt (g (v ∘ some)) (v none)
  have hcont : P.Definable L {v | cont v} := by
    have h := definable_positive_quantifier F hF (Q := fun a e => ∀ᶠ y in 𝓝 (a none), |g (a ∘ some) y-g (a ∘ some) (a none)| < e)
      (definable_fiber_germ F hF (.inl none) test close) true
    convert h using 1
    ext v; exact continuousAt_order_ball _ _
  let zero (a : U → K) (y : K) := g (a ∘ some) y = 0
  have dZero : P.Definable L {w : B → K | zero (w ∘ Sum.inl) (w (.inr ()))} := by
    let ρ : U → B := (Option.elim · (.inr ()) (Sum.inl ∘ some))
    have term := (t.relabel ρ).definableFun_realize.of_empty (A := P)
    convert term.ofPred_eq (definable_const_of_closed_term F.zero 0 hF.zero) using 1
    ext w
    change t.realize _ = 0 ↔ (t.relabel ρ).realize w = 0
    rw [Term.realize_relabel]
    have he : (fun j : U => j.elim (w (.inr ())) ((w ∘ Sum.inl) ∘ some)) = w ∘ ρ := by funext j; cases j <;> rfl
    rw [he]
  have zG := definable_fiber_germ F hF none zero dZero
  have nG := definable_fiber_germ F hF none (fun v y => ¬zero v y) dZero.compl
  convert hcont.compl.union (zG.compl.inter nG.compl) using 1
  ext v
  simp only [criticalSet,frontier_eq_inter_compl_interior,mem_union,mem_compl_iff,mem_inter_iff,
    mem_interior_iff_mem_nhds,mem_ofPred_eq]
  rfl

private theorem cell_frontier_finite {C : Set K} (h : IsUnaryCell C) : (frontier C).Finite := by
  rcases h with rfl | ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · simp
  · exact (finite_singleton a).subset isClosed_singleton.frontier_subset
  · rw [frontier_Iio]; exact finite_singleton _
  · rw [frontier_Ioi]; exact finite_singleton _
  · by_cases lt : a < b
    · rw [frontier_Ioo lt]; exact (finite_singleton _).insert _
    · simp [Ioo_eq_empty lt]

/-- The remaining pointwise finiteness input to 3.3 follows from the
ordinary unary o-minimal partition. Discontinuities at cell boundaries
and the boundary points of the zero set are included explicitly. -/
theorem finite_critical_of_unary_cells (g : K → K) (omin : IsOMinimal (K := K) L)
    (zero : (univ : Set K).Definable₁ L (g ⁻¹' {0}))
    (C : Finset (Set K)) (cover : (⋃ B ∈ C, B) = univ)
    (pieces : ∀ B ∈ C, IsUnaryCell B ∧ ContinuousOn g B) : (criticalSet g).Finite := by
  obtain ⟨Z,hZ,z⟩ := omin _ zero
  have boundary : (frontier (g ⁻¹' {0})).Finite := by
    rw [z]
    exact (Z.finite_toSet.biUnion (fun B hb => cell_frontier_finite (hZ B hb))).subset
      (Z.frontier_biUnion_subset id)
  apply Set.Finite.union _ boundary
  apply (C.finite_toSet.biUnion (fun B hb => cell_frontier_finite (pieces B hb).1)).subset
  intro x fail
  obtain ⟨B,hB,hx⟩ := mem_iUnion₂.mp (cover.symm ▸ mem_univ x)
  refine mem_iUnion₂.mpr ⟨B,hB,(mem_frontier_iff_notMem_interior hx).mpr ?_⟩
  exact fun inner => fail (((pieces B hB).2 x hx).continuousAt (mem_interior_iff_mem_nhds.mp inner))

include hF in
/-- Uniform finiteness from o-minimality is needed only for the
one definable family constructed here. Each value is a genuine term
critical point. This supplies the ordered-branch input to 3.3. -/
theorem critical_family_of_uniform_finiteness (T : Finset (L.Term (Option I)))
    (finite : ∀ t ∈ T, ∀ a : I → K, (criticalSet (fun y => t.realize (Option.elim · y a))).Finite)
    (uniform : ∀ U : (I → K) → Finset K, (∅ : Set K).Definable L {w : Option I → K | w none ∈ U (w ∘ some)} →
      ∃ N, ∀ a, (U a).card ≤ N) :
    ∃ (N : ℕ) (S : (I → K) → Finset K),
      (∅ : Set K).Definable L {v : Option I → K | v none ∈ S (v ∘ some)} ∧ (∀ a, (S a).card ≤ N) ∧
      ∀ a (j : T), criticalSet (fun y => j.val.realize (Option.elim · y a)) ⊆ S a := by
  classical
  let S (a : I → K) := (finite_iUnion (fun t : T => finite t.val t.property a)).toFinset
  have defS : (∅ : Set K).Definable L {v : Option I → K | v none ∈ S (v ∘ some)} := by
    convert definable_iUnion_of_finite (fun t : T => definable_term_critical_family (P := (∅ : Set K)) F hF t.val) using 1
    ext v; simp [S]
  obtain ⟨N,hN⟩ := uniform S defS
  exact ⟨N,S,defS,hN,fun a j _ hx => (Set.Finite.mem_toFinset _).mpr (mem_iUnion_of_mem j hx)⟩

variable {E : Type*} {J : Type _}

include hF in
/-- Lemma 3.3 from sorted QE, o-minimal unary continuity cells and
uniform finiteness. After a field input is fixed the branch list works
simultaneously for all auxiliary inputs. -/
theorem piecewise_field_functions_of_ominimality (O : ValuationSubring K) [L.Structure (Residue O)]
    (hO : IsOrderConvex O) (powers : E → RV0 O → RV0 O)
    (only : ∀ {n} (r : L.Relations n), ∃ e : n = 2, e ▸ r = F.le)
    (f : (I → K) → (J → RV0 O) → K) (φ : SortedFormula L E (FunctionGraphVars I J))
    (graph : ∀ x t y, φ.realize (canonicalStructure (L := L) O hO powers) (graphAssignment O x t y) ↔ y = f x t)
    (qe : ∃ ψ : SortedFormula L E (FunctionGraphVars I J), ψ.IsQF ∧
      ∀ v, ψ.realize (canonicalStructure (L := L) O hO powers) v ↔ φ.realize (canonicalStructure (L := L) O hO powers) v)
    {e : K} (he : 0 < e) (heO : O.valuation e < 1) (omin : IsOMinimal (K := K) L)
    (continuity : ∀ g : K → K, (univ : Set K).DefinableFun L (fun v : Fin 1 → K => g (v 0)) →
      ∃ C : Finset (Set K), (⋃ B ∈ C, B) = univ ∧ ∀ B ∈ C, IsUnaryCell B ∧ ContinuousOn g B)
    (uniform : ∀ U : (I → K) → Finset K, (∅ : Set K).Definable L {w : Option I → K | w none ∈ U (w ∘ some)} →
      ∃ N, ∀ a, (U a).card ≤ N) :
    ∃ (N : ℕ) (g : Fin N → (I → K) → K), (∀ i, (∅ : Set K).DefinableFun L (g i)) ∧
      (∀ a t, ∃! i, f a t = g i a ∧ ∀ j < i, f a t ≠ g j a) ∧ ∀ a, (range (f a)).Finite := by
  apply piecewise_field_functions_of_qe O hO powers F hF only f φ graph qe he heO
  intro T
  apply critical_family_of_uniform_finiteness F hF T _ uniform
  intro t _ a
  let g (y : K) := t.realize (Option.elim · y a)
  have dg : (univ : Set K).DefinableFun L (fun v : Fin 1 → K => g (v 0)) := by
    let ρ : Option I → (univ : Set K) ⊕ Option (Fin 1) :=
      (Option.elim · (.inr (some 0)) (fun j => .inl ⟨a j,mem_univ _⟩))
    apply definable_iff_exists_formula_sum.mpr
    refine ⟨(t.relabel ρ).equal (.var (.inr none)),?_⟩
    ext v
    change g (v (some 0)) = v none ↔ _
    simp only [mem_ofPred_eq,Formula.realize_equal,Term.realize_relabel,Term.realize_var,Sum.elim_inr]
    have he : Sum.elim Subtype.val v ∘ ρ = (Option.elim · (v (some 0)) a) := by funext j; cases j <;> rfl
    rw [he]
  obtain ⟨C,covers,cont⟩ := continuity g dg
  exact finite_critical_of_unary_cells g omin (dg.ofPred_eq (L.definableFun_const _ (mem_univ 0))) C covers cont

end GeneralizedEuler.Section3
