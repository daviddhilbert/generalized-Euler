module

public import Section3.BoundaryFieldTerms
import all Section3.BoundaryGraphFormula
import all Section3.BoundaryBranches
import all Section3.DefinableBoundary
import all Section2.SortedSyntax

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set
universe u
variable {L : Language.{u,u}} {E : Type u} {V X : TCsort → Type u} {n : ℕ}

/-- Extra names for the input RV label vector and a test value of the
output. Neither belongs to the base of the partition pieces. -/
abbrev FiberTestVars (V : TCsort → Type u) (n : ℕ) := AddSortedVar (AddSortedBlock V .rv n) .rv

abbrev fiberInput (j : Fin n) : FiberTestVars V n .rv := .inl (.inr ⟨j,⟨rfl⟩⟩)
private def fiberOutput : FiberTestVars V n .rv := .inr ⟨rfl⟩
private def fiberForm (V : TCsort → Type u) (n : ℕ) :
    SortedFormula L E (AddSortedBlock (FiberTestVars V n) .vf n) :=
  everyCoord fun j => .equal (rvOf (.var (.inr ⟨j,⟨rfl⟩⟩))) (.var (.inl (fiberInput j)))

private theorem fiberForm_realize (M : SortedStructure L E X) (p : ∀ s, FiberTestVars V n s → X s)
    (a : Fin n → X .vf) : (fiberForm V n).realize M (appendSortedBlock p a) ↔
      M.rvMap ∘ a = p .rv ∘ fiberInput := by
  simp only [fiberForm,everyCoord_realize,SortedFormula.realize,rvOf_realize,SortedTerm.realize]
  exact funext_iff.symm

/-- Existential witnesses on both sides of a single cut. -/
private def fiberSplit (χ : SortedFormula L E (AddSortedBlock (FiberTestVars V n) .vf n)) :
    SortedFormula L E (FiberTestVars V n) :=
  (((fiberForm V n).conjunction χ).exBlock .vf n).conjunction
    (((fiberForm V n).conjunction χ.neg).exBlock .vf n)

private theorem fiberSplit_realize (M : SortedStructure L E X) (p : ∀ s, FiberTestVars V n s → X s)
    (χ : SortedFormula L E (AddSortedBlock (FiberTestVars V n) .vf n)) :
    (fiberSplit χ).realize M p ↔ (∃ a, M.rvMap ∘ a = p .rv ∘ fiberInput ∧ χ.realize M (appendSortedBlock p a)) ∧
      (∃ b, M.rvMap ∘ b = p .rv ∘ fiberInput ∧ ¬ χ.realize M (appendSortedBlock p b)) := by
  simp only [fiberSplit,SortedFormula.realize_conjunction,SortedFormula.realize_exBlock,
    fiberForm_realize,SortedFormula.realize_neg]

private def addLabelNames (s : TCsort) :
    AddSortedBlock V .vf n s → AddSortedBlock (FiberTestVars V n) .vf n s :=
  Sum.elim (fun j => .inl (.inl (.inl j))) Sum.inr

abbrev baseOf (p : ∀ s, FiberTestVars V n s → X s) (s : TCsort) (i : V s) : X s :=
  p s (.inl (.inl i))

private theorem baseAssignment (p : ∀ s, FiberTestVars V n s → X s) (a : Fin n → X .vf) :
    (fun s => appendSortedBlock p a s ∘ addLabelNames s) = appendSortedBlock (baseOf p) a := by
  funext s z
  cases z <;> rfl

private def outputTest (t : SortedTerm L E (AddSortedBlock V .vf n) .vf) :
    SortedFormula L E (AddSortedBlock (FiberTestVars V n) .vf n) :=
  .equal (rvOf (t.relabel addLabelNames)) (.var (.inl fiberOutput))

private theorem outputTest_realize (M : SortedStructure L E X) (p : ∀ s, FiberTestVars V n s → X s)
    (t : SortedTerm L E (AddSortedBlock V .vf n) .vf) (a : Fin n → X .vf) :
    (outputTest t).realize M (appendSortedBlock p a) ↔ branchAt M (baseOf p) t a = p .rv fiberOutput := by
  simp only [outputTest,SortedFormula.realize,rvOf_realize,SortedTerm.realize_relabel,baseAssignment]
  rfl

/-- The compactness and partition step of 3.16, in the form needed for
3.26. The pointwise input on a fiber in one type is the consequence of
3.15: two realizations in that fiber agree on the term's leading value.
The tests defining the pieces use only the original variables. -/
theorem finite_term_fiber_partition (T : SortedTheory L E) (M : SortedStructure L E X)
    (v : ∀ s, V s → X s) (hne : ∀ s, Nonempty (X s)) (hT : ∀ φ ∈ T, φ.realize M)
    [Zero (X .rv)] (hz : ∀ p : (∀ s, FiberTestVars V n s → X s), rvZeroTerm.realize M p = 0)
    (t : SortedTerm L E (AddSortedBlock V .vf n) .vf)
    (tests : Set (SortedFormula L E (AddSortedBlock V .vf n)))
    (rigid : ∀ P : T.PointedModel (FiberTestVars V n),
      (∀ j, P.point .rv (fiberInput j) ≠ rvZeroTerm.realize P.model P.point) →
      (∀ χ ∈ tests, ∀ a b : Fin n → P.carrier .vf,
        P.model.rvMap ∘ a = P.point .rv ∘ fiberInput → P.model.rvMap ∘ b = P.point .rv ∘ fiberInput →
        (χ.realize P.model (appendSortedBlock (baseOf P.point) a) ↔
          χ.realize P.model (appendSortedBlock (baseOf P.point) b))) →
      ∀ a b : Fin n → P.carrier .vf,
        P.model.rvMap ∘ a = P.point .rv ∘ fiberInput → P.model.rvMap ∘ b = P.point .rv ∘ fiberInput →
        branchAt P.model (baseOf P.point) t a = branchAt P.model (baseOf P.point) t b) :
    ∃ (k : ℕ) (B : Fin k → Set (Fin n → X .vf)), (∀ j, BlockDefinable M v .vf (B j)) ∧
      (∀ a, ∃ j, a ∈ B j) ∧ ∀ j u, (∀ l, u l ≠ 0) →
      (∀ a : Fin n → X .vf, M.rvMap ∘ a = u → a ∈ B j) →
      ∀ a b : Fin n → X .vf, M.rvMap ∘ a = u → M.rvMap ∘ b = u → branchAt M v t a = branchAt M v t b := by
  classical
  let pos : SortedFormula L E (FiberTestVars V n) := everyCoord (fun j => (SortedFormula.equal (.var (fiberInput (V := V) (n := n) j)) rvZeroTerm).neg)
  let bad := pos.conjunction (fiberSplit (outputTest t))
  let cut (χ : tests) := fiberSplit (χ.val.relabel addLabelNames)
  obtain ⟨schemes,cover⟩ := T.exists_finite_formula_cover bad cut (by
    intro P hp
    obtain ⟨nz,wit⟩ := (SortedFormula.realize_conjunction P.model P.point _ _).mp hp
    obtain ⟨⟨a,ha,yes⟩,b,hb,no⟩ := (fiberSplit_realize _ _ _).mp wit
    by_contra! empty
    have hnz := (everyCoord_realize _ _ _).mp nz
    simp only [SortedFormula.realize_neg,SortedFormula.realize,SortedTerm.realize] at hnz
    have same := rigid P hnz (by
      intro χ hχ x y hx hy
      have hn := empty (⟨χ,hχ⟩ : tests)
      have unsplit := mt (fiberSplit_realize P.model P.point (χ.relabel addLabelNames)).mpr hn
      simp only [SortedFormula.realize_relabel,baseAssignment] at unsplit
      constructor <;> intro h <;> by_contra h'
      · exact unsplit ⟨⟨x,hx,h⟩,y,hy,h'⟩
      · exact unsplit ⟨⟨y,hy,h⟩,x,hx,h'⟩) a b ha hb
    exact no ((outputTest_realize _ _ _ _).mpr (same ▸ (outputTest_realize _ _ _ _).mp yes)))
  let Pattern := schemes → Bool
  let e := Fintype.equivFin Pattern
  let cell (p : Pattern) (a : Fin n → X .vf) := ∀ χ : schemes,
    χ.val.val.realize M (appendSortedBlock v a) ↔ p χ = true
  refine ⟨Fintype.card Pattern,fun j => {a | cell (e.symm j) a},?_,?_,?_⟩
  · intro j
    let p := e.symm j
    let χ (h : schemes) := if p h then h.val.val else h.val.val.neg
    refine ⟨SortedFormula.allOf (Finset.univ.toList.map χ),fun a => ?_⟩
    rw [SortedFormula.realize_allOf]
    simp only [List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,forall_exists_index,forall_apply_eq_imp_iff]
    apply forall_congr'
    intro h
    change (χ h).realize M (appendSortedBlock v a) ↔ (_ ↔ p h = true)
    cases hp : p h <;> simp [χ,hp,SortedFormula.realize_neg]
  · intro a
    let p : Pattern := fun χ => decide (χ.val.val.realize M (appendSortedBlock v a))
    exact ⟨e p,by change cell (e.symm (e p)) a; simp [cell,p]⟩
  · intro j u nz full a b ha hb
    by_contra dif
    let w := appendSortedBlock v u
    let p := extendSortedAssignment w (branchAt M v t a)
    let P : T.PointedModel (FiberTestVars V n) := ⟨X,M,p,hne,hT⟩
    have base : baseOf p = v := rfl
    have eqFiber : p .rv ∘ fiberInput = u := rfl
    have hp : P.realizes bad := by
      apply (SortedFormula.realize_conjunction _ _ _ _).mpr
      refine ⟨(everyCoord_realize _ _ _).mpr (fun l => ?_), (fiberSplit_realize _ _ _).mpr ?_⟩
      · rw [SortedFormula.realize_neg]
        change u l ≠ rvZeroTerm.realize M p
        simpa [hz] using nz l
      · have yes := (outputTest_realize M p t a).mpr (by rw [base]; rfl)
        refine ⟨⟨a,ha,yes⟩,b,hb,fun no => dif ?_⟩
        have he := (outputTest_realize M p t b).mp no
        rw [base] at he
        exact he.symm
    obtain ⟨χ,hχ,hs⟩ := cover P hp
    obtain ⟨⟨x,hx,xin⟩,y,hy,yout⟩ := (fiberSplit_realize _ _ _).mp hs
    change (χ.val.relabel addLabelNames).realize M (appendSortedBlock p x) at xin
    change ¬ (χ.val.relabel addLabelNames).realize M (appendSortedBlock p y) at yout
    simp only [SortedFormula.realize_relabel,baseAssignment,base] at xin yout
    exact yout ((full y (hy.trans eqFiber) ⟨χ,hχ⟩).mpr ((full x (hx.trans eqFiber) ⟨χ,hχ⟩).mp xin))

end GeneralizedEuler.Section3
