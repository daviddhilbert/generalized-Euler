module

public import Section3.DifferentialPolynomial
public import Section2.DefinableResidueCharts
import all Section3.AdjacentCharts
import all Section3.ContractedJets
import all Section2.ResidueTopology

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set Filter
open scoped Topology

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
variable [hO : Fact (IsOrderConvex O)] {n : ℕ}
noncomputable local instance : LinearOrder (Residue O) := residueLinearOrder O hO.out
local instance : IsOrderedRing (Residue O) := residue_isOrderedRing O hO.out
noncomputable local instance : TopologicalSpace (Residue O) := residueOrderTopology O hO.out
local instance : OrderTopology (Residue O) := ⟨rfl⟩

variable {L : Language} [L.Structure (Residue O)] {P : Set (Residue O)} {A : Set (Fin n → Residue O)}
  {p : Fin n → ℕ} {g : (Fin n → Residue O) → Residue O}

/-- The RV iteration assertion of 3.31. On the common good locus, if
no adjacent derivative vanishes or drops in magnitude, every mixed
derivative of a nonzero chart of the original contraction recovers the
leading term of the corresponding field jet. The same open locus
works for every scale and every order of differentiation. -/
theorem SmoothJetData.iterated_leading_terms (D : SmoothJetData O L P p A g) (F : OrderedFieldTerms L)
    (hF : InterpretsOrderedFieldTerms (A := Residue O) F)
    (front : ∀ S : Set (Fin n → Residue O), (univ : Set (Residue O)).Definable L S → IsNowhereDense (frontier S)) :
    ∃ W ⊆ D.domain, P.Definable L W ∧ P.Definable L (D.domain \ W) ∧ IsOpen W ∧
      projectionDimensionWithBot (D.domain \ W) < (n : WithBot ℕ) ∧
      ((∀ a, (IsLocalRing.residue O) ∘ a ∈ W → ∀ q ≤ p, ∀ i, q i ≠ 0 →
        ¬ (D.field q a = 0 ∨ O.valuation (D.field q a) < O.valuation (D.field (Function.update q i (q i-1)) a))) →
      ∀ t ∈ W, ∀ c : K, c ≠ 0 → unsignedValue O (D.leading 0 t) = O.valuation c →
        ∀ w, wordIndex w ≤ p → D.leading (wordIndex w) t = rv O c * residueRV O
          (iteratedOrderPartial (fun u => scaledResidue O (D.leading 0 u) c) w t)) := by
  classical
  obtain ⟨W,sub,dW,dE,op,dim,localVal,adj⟩ := contracted_jets_on_open_value_locus O hO.out F p D.domain
    D.field D.leading D.definable D.contracts D.integral D.finiteValues D.valueEquality hF front D.meanValue D.smooth
  refine ⟨W,sub,dW,dE,op,dim,fun never t ht c cn hc => ?_⟩
  let J (q : Fin n → ℕ) (s : Fin n → Residue O) := scaledResidue O (D.leading q s) c
  let chart := {u ∈ W | unsignedValue O (D.leading 0 u) = O.valuation c}
  have atCenter : t ∈ interior chart := mem_interior_iff_mem_nhds.mpr
    (((show ∀ᶠ u in 𝓝 t, u ∈ W from op.mem_nhds ht).and (localVal t ht 0 (by exact bot_le))).mono (fun _ hu => ⟨hu.1,hu.2.trans hc⟩))
  have lift (u : Fin n → Residue O) : ∃ a : Fin n → O, (IsLocalRing.residue O) ∘ a = u := by
    choose a ha using fun j => IsLocalRing.residue_surjective (u j)
    exact ⟨a,funext ha⟩
  have equalValues (a : Fin n → O) (u : Fin n → Residue O) (ha : (IsLocalRing.residue O) ∘ a = u)
      (hu : u ∈ chart) : ∀ q ≤ p, O.valuation (D.field q a) = O.valuation c := by
    apply all_partials_of_adjacent p
    · rw [←unsignedValue_rv O, D.contracts 0 (by exact bot_le) a (ha ▸ sub hu.1),ha]; exact hu.2
    · intro q hq i hi prev
      have cmp := ((adj a (ha ▸ hu.1)).2 q hq i hi).1.1
      simp only [Function.update_eq_self] at cmp
      have no := never a (ha ▸ hu.1) q hq i hi
      exact (le_antisymm cmp (le_of_not_gt (fun h => no (Or.inr h)))).trans prev
  have derivatives (q : Fin n → ℕ) (hq : q ≤ p) (i : Fin n) (hi : q i ≠ 0) (u : Fin n → Residue O)
      (hu : u ∈ interior chart) : HasOrderDerivativeAt (fun v => J (Function.update q i (q i-1)) (Function.update u i v)) (u i) (J q u) := by
    obtain ⟨a,rfl⟩ := lift u
    let j := Function.update q i (q i-1)
    have inc := interior_subset hu
    have cmp := ((adj a inc.1).2 q hq i hi).1.2.1
    simp only [Function.update_eq_self] at cmp
    have jle : j ≤ p := (pred_le q i).trans hq
    obtain ⟨s,_,der,eqn⟩ := (cmp c cn (equalValues a _ rfl inc j jle).symm).mp (never a inc.1 q hq i hi)
    have js : J q (IsLocalRing.residue O ∘ a) = s := by
      change rvResidue O (D.leading q _ / rv O c) = s
      rw [←D.contracts q hq a (sub inc.1),eqn]
      have cancel : (rv O c * residueRV O s) / rv O c = residueRV O s :=
        (div_eq_iff (G₀ := RV0 O) ((rv_eq_zero_iff O).not.mpr cn)).mpr (mul_comm (G := RV0 O) _ _)
      rw [cancel,rvResidue_residueRV]
    rw [js]; exact der
  intro w hw
  have it := iterated_of_adjacent isOpen_interior J derivatives w hw atCenter
  change D.leading (wordIndex w) t = rv O c * residueRV O (iteratedOrderPartial (J 0) w t)
  rw [it]
  obtain ⟨a,ha⟩ := lift t
  have eqv : unsignedValue O (D.leading (wordIndex w) t) = unsignedValue O (rv O c) := by
    rw [←ha,←D.contracts _ hw a (ha ▸ sub ht),unsignedValue_rv,unsignedValue_rv]
    exact equalValues a t ha (interior_subset atCenter) _ hw
  change _ = rv O c * residueRV O (rvResidue O (_ / rv O c))
  rw [residueRV_rvResidue_of_mem_range O (div_mem_residueRV_of_equal_unsignedValue O eqv),
    mul_div_cancel₀ (G₀ := RV0 O) _ ((rv_eq_zero_iff O).not.mpr cn)]

end GeneralizedEuler.Section3
