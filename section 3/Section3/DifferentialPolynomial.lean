module

public import Section3.IteratedReduction
import all Section3.AdjacentCharts
import all Section3.ContractedJets
import all Section3.ReducedJets
import all Section2.ResidueTopology

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set
open scoped Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
variable [hO : Fact (IsOrderConvex O)] {n : ℕ}

noncomputable local instance : LinearOrder (Residue O) := residueLinearOrder O hO.out
local instance : IsOrderedRing (Residue O) := residue_isOrderedRing O hO.out
noncomputable local instance : TopologicalSpace (Residue O) := residueOrderTopology O hO.out
local instance : OrderTopology (Residue O) := ⟨rfl⟩

/-- Data available before applying 3.31 in the proof of 3.32. The
initial smooth label set is allowed to depend on the component of the
operator. Values of functions and their chosen extensions off that set
are unrestricted. -/
structure SmoothJetData (L : Language) [L.Structure (Residue O)] (P : Set (Residue O)) (p : Fin n → ℕ)
    (A : Set (Fin n → Residue O)) (g : (Fin n → Residue O) → Residue O) where
  domain : Set (Fin n → Residue O)
  subset : domain ⊆ A
  definable : P.Definable L domain
  small : projectionDimensionWithBot (A \ domain) < (n : WithBot ℕ)
  field : (Fin n → ℕ) → (Fin n → O) → K
  leading : (Fin n → ℕ) → (Fin n → Residue O) → RV0 O
  contracts : ∀ q ≤ p, ∀ a, (IsLocalRing.residue O) ∘ a ∈ domain → rv O (field q a) = leading q ((IsLocalRing.residue O) ∘ a)
  integral : ∀ a, (IsLocalRing.residue O) ∘ a ∈ domain → field 0 a ∈ O
  reduces : ∀ a, (IsLocalRing.residue O) ∘ a ∈ domain → totalResidue O (field 0 a) = g ((IsLocalRing.residue O) ∘ a)
  finiteValues : ∀ q ≤ p, ((unsignedValue O) ∘ leading q '' domain).Finite
  valueEquality : ∀ q ≤ p, P.Definable L {w : Fin n ⊕ Fin n → Residue O |
    unsignedValue O (leading q (w ∘ Sum.inl)) = unsignedValue O (leading q (w ∘ Sum.inr))}
  meanValue : ∀ q ≤ p, ∀ i, q i ≠ 0 → ∀ (a : Fin n → O) l u,
    MapsTo (Function.update ((IsLocalRing.residue O) ∘ a) i) (Ioo l u) domain →
    PiecewiseSliceMVT O (Ioo l u) (fun y => field (Function.update q i (q i-1)) (Function.update a i y))
      (fun y => field q (Function.update a i y))
  smooth : ∀ q ≤ p, ∀ (a : Fin n → O) i l u,
    MapsTo (Function.update ((IsLocalRing.residue O) ∘ a) i) (Ioo l u) domain →
    SmoothSliceChart O hO.out (Ioo l u) (fun y => field q (Function.update a i y))
      (fun s => leading q (Function.update ((IsLocalRing.residue O) ∘ a) i s))

variable {L : Language} [L.Structure (Residue O)] {P : Set (Residue O)} {A : Set (Fin n → Residue O)}
variable {g : (Fin n → Residue O) → Residue O} {p : Fin n → ℕ}

theorem SmoothJetData.reduce_words (D : SmoothJetData O L P p A g) (F : OrderedFieldTerms L)
    (hF : InterpretsOrderedFieldTerms (A := Residue O) F)
    (front : ∀ S : Set (Fin n → Residue O), (univ : Set (Residue O)).Definable L S → IsNowhereDense (frontier S))
    (tame : ∀ B : Set (Fin n → Residue O), P.Definable L B → interior B = ∅ → IsNowhereDense B)
    (dA : P.Definable L A) :
    ∃ W ⊆ A, P.Definable L (A \ W) ∧ IsOpen W ∧ projectionDimensionWithBot (A \ W) < (n : WithBot ℕ) ∧
      ∀ a, (IsLocalRing.residue O) ∘ a ∈ W → ∀ w, wordIndex w ≤ p →
        D.field (wordIndex w) a ∈ O ∧ totalResidue O (D.field (wordIndex w) a) =
          iteratedOrderPartial g w ((IsLocalRing.residue O) ∘ a) := by
  classical
  obtain ⟨W,sub,dW,dE,op,dim,adj⟩ := contracted_jets_on_open_locus O hO.out F p D.domain D.field D.leading
    D.definable D.contracts D.integral D.finiteValues D.valueEquality hF front D.meanValue D.smooth
  let red (q : Fin n → ℕ) (t : Fin n → Residue O) := rvResidue O (D.leading q t)
  let J (q : Fin n → ℕ) := if q = 0 then g else red q
  have lift (t : Fin n → Residue O) : ∃ a : Fin n → O, (IsLocalRing.residue O) ∘ a = t := by
    choose a ha using fun j => IsLocalRing.residue_surjective (t j)
    exact ⟨a,funext ha⟩
  have agree (q) (t) (ht : t ∈ W) : red q t = J q t := by
    by_cases qz : q = 0
    · subst q
      obtain ⟨a,rfl⟩ := lift t
      simp only [J,ite_eq_left rfl,red]
      rw [←D.contracts 0 (by exact bot_le) a (sub ht),rvResidue_rv]
      exact D.reduces a (sub ht)
    · simp [J,qz]
  have slope (q) (hq : q ≤ p) (i) (nz : q i ≠ 0) (t) (ht : t ∈ W) :
      HasOrderDerivativeAt (fun u => J (Function.update q i (q i-1)) (Function.update t i u)) (t i) (J q t) := by
    obtain ⟨a,rfl⟩ := lift t
    let t := (IsLocalRing.residue O) ∘ a
    have hd := ((adj a ht).2 q hq i nz).2
    rw [←agree q t ht]
    have cont : Continuous (Function.update t i) := continuous_pi (fun j => by
      by_cases h : j = i
      · subst j; simp only [Function.update_self]; exact continuous_id
      · simpa only [Function.update_of_ne h] using (continuous_const : Continuous (fun _ : Residue O => t j)))
    have center : t i ∈ (Function.update t i) ⁻¹' W := by simpa only [mem_preimage,Function.update_eq_self]
    obtain ⟨δ,pos,near⟩ := interval_around (op.preimage cont) center
    exact derivative_of_agreement_near hd pos (fun y hy => agree _ _ (near y hy))
  have thin := (tame _ (dA.sdiff D.definable) (dimensionWithBot_lt_arity_iff.mp D.small)).union
    (tame _ dE (dimensionWithBot_lt_arity_iff.mp dim))
  have incl : A \ W ⊆ (A \ D.domain) ∪ (D.domain \ W) := by
    intro x hx; by_cases h : x ∈ D.domain
    · exact Or.inr ⟨h,hx.2⟩
    · exact Or.inl ⟨hx.1,h⟩
  refine ⟨W,sub.trans D.subset,dA.sdiff dW,op,dimensionWithBot_lt_arity_iff.mpr
    (eq_empty_of_subset_empty ((interior_mono subset_closure).trans (thin.mono incl).subset)),?_⟩
  intro a ha w hw
  let t := (IsLocalRing.residue O) ∘ a
  have eqn := iterated_of_adjacent op J slope w hw ha
  have base : J 0 = g := by simp [J]
  rw [base] at eqn
  refine ⟨(adj a ha).1 _ hw,?_⟩
  rw [eqn,←agree _ t ha]
  change totalResidue O _ = rvResidue O (D.leading _ _)
  rw [←D.contracts _ hw a (sub ha),rvResidue_rv]

/-- Evaluation of a differential polynomial with definable contractible
coefficients on all representatives of every surviving label. Each
variable specifies a component and an ordered list of derivatives of
that component. The exceptional set is independent of representatives. -/
theorem reduce_differential_polynomial {I : Type*} [Finite I] (g : I → (Fin n → Residue O) → Residue O)
    (order : I → Fin n → ℕ) (word : I → List (Fin n)) (hw : ∀ i, wordIndex (word i) ≤ order i)
    (D : ∀ i, SmoothJetData O L P (order i) A (g i)) (F : OrderedFieldTerms L)
    (hF : InterpretsOrderedFieldTerms (A := Residue O) F) (dA : P.Definable L A)
    (front : ∀ S : Set (Fin n → Residue O), (univ : Set (Residue O)).Definable L S → IsNowhereDense (frontier S))
    (tame : ∀ B : Set (Fin n → Residue O), P.Definable L B → interior B = ∅ → IsNowhereDense B)
    (poly : (Fin n → O) → MvPolynomial I O) (coeff : (Fin n → Residue O) → MvPolynomial I (Residue O))
    (contract : ∀ a, (IsLocalRing.residue O) ∘ a ∈ A → MvPolynomial.map (IsLocalRing.residue O) (poly a) =
      coeff ((IsLocalRing.residue O) ∘ a)) :
    ∃ V ⊆ A, P.Definable L V ∧ projectionDimensionWithBot V < (n : WithBot ℕ) ∧
      ∀ a, (IsLocalRing.residue O) ∘ a ∈ A \ V → ∃ u : I → O,
        (∀ i, (u i : K) = (D i).field (wordIndex (word i)) a) ∧
        IsLocalRing.residue O (MvPolynomial.eval u (poly a)) =
          MvPolynomial.eval (fun i => iteratedOrderPartial (g i) (word i) ((IsLocalRing.residue O) ∘ a))
            (coeff ((IsLocalRing.residue O) ∘ a)) := by
  choose W sub defE _ dim good using fun i => (D i).reduce_words O F hF front tame dA
  obtain ⟨V,subV,dV,dimV,inc⟩ := finite_label_exceptions A (fun i => A \ W i)
    (fun i => ⟨sdiff_subset,defE i,dim i⟩) tame
  refine ⟨V,subV,dV,dimV,?_⟩
  intro a ha
  have inside i : (IsLocalRing.residue O) ∘ a ∈ W i := by_contra (fun h => ha.2 (inc i ⟨ha.1,h⟩))
  let u (i : I) : O := ⟨_,(good i a (inside i) (word i) (hw i)).1⟩
  refine ⟨u,fun _ => rfl,?_⟩
  rw [←contract a ha.1]
  apply residue_differential_polynomial
  intro i
  have he := (good i a (inside i) (word i) (hw i)).2
  rw [totalResidue_of_mem O (u i).property] at he
  exact he

end GeneralizedEuler.Section3
