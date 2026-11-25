module

public import Section3.AtomicDiscs
public import Section3.DiscGraphImages
public import Section3.ClosedDiscPoints
import all Section3.DiscGraphImages
import all Section3.DiscAtomicSlices
import all Section3.Atomicity
import all Section2.ValuativeDisc

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
    (O : ValuationSubring K) (hO : IsOrderConvex O)

def openDiscRepresentatives (D : Set K) (r : O.ValueGroup) :=
  {w : Fin 2 → K | openDisc O (w 0) (O.valuation (w 1)) = D ∧ O.valuation (w 1) = r}

include hO in
/-- Lemma 3.22 from saturation for ordinary field formulas. A type on
one center asks that its disc lie in A and that each old unary formula
be constant on that disc. Substituting the running point as center and
one fixed radius representative removes both imaginary names from each
test used to prove atomicity. -/
theorem saturated_atomic_open_disc {I : Type*} [Infinite I] (P : Set K) (A : Set K)
    (b : K) (bn : b ≠ 0) (centers : I → K)
    (inj : Function.Injective (fun i => openDisc O (centers i) (O.valuation b)))
    (inside : ∀ i, openDisc O (centers i) (O.valuation b) ⊆ A)
    (F : FieldTerms (convexLanguage L)) :
    letI := convexStructure O L
    InterpretsFieldTerms (K := K) F → P.Definable₁ (convexLanguage L) A →
    (∀ φ : (convexLanguage L).Formula ((P ⊕ Unit) ⊕ Unit),
      FiniteConvexUnion {x : K | φ.Realize (Sum.elim (Sum.elim Subtype.val (fun _ => b)) (fun _ => x))}) →
    RealizesFinitelySatisfiableFieldTypes (convexLanguage L) K (P ⊕ Unit) →
    ∃ c : K, let D := openDisc O c (O.valuation b)
      D ⊆ A ∧ AtomicOver (UnaryOverClass (L := convexLanguage L) P (openDiscRepresentatives O D (O.valuation b))) D := by
  classical
  let := convexStructure O L
  intro hF dA hnf sat
  obtain ⟨α,hα⟩ := definable_iff_exists_formula_sum.mp dA
  let J := convexLanguage L
  let N := P ⊕ Unit
  let V := N ⊕ Unit
  let Z := V ⊕ Unit
  let p : N → K := Sum.elim Subtype.val (fun _ => b)
  let z : Z := .inr ()
  let x : Z := .inl (.inr ())
  let w : Z := .inl (.inl (.inr ()))
  let ball := discMemberFormula F false (.var z) (.var x) (.var w)
  let body := α.relabel (Sum.elim (fun a => .inl (.inl (.inl a))) (fun _ => z))
  let outer := Formula.iAlls Unit (ball.imp body)
  let rebind := Sum.elim (fun a : N => (.inl (.inl a) : Z)) (fun _ : Unit => z)
  let req (φ : J.Formula V) := outer ⊓ Formula.iAlls Unit
    (ball.imp ((φ.relabel rebind).iff (φ.relabel Sum.inl)))
  let test (φ : J.Formula V) (x : K) := φ.Realize (Sum.elim p (fun _ => x))
  have ballEval (c : K) (s : Unit → K) : ball.Realize (Sum.elim (Sum.elim p (fun _ => c)) s) ↔
      s () ∈ openDisc O c (O.valuation b) := realize_discMemberFormula O hF false _ _ _ _
  have bodyEval (c : K) (s : Unit → K) : body.Realize (Sum.elim (Sum.elim p (fun _ => c)) s) ↔ s () ∈ A := by
    rw [Formula.realize_relabel]
    have he : Sum.elim (Sum.elim p (fun _ => c)) s ∘ Sum.elim (fun a : P => (.inl (.inl (.inl a)) : Z)) (fun _ : Fin 1 => z) =
        Sum.elim Subtype.val (fun _ => s ()) := by funext j; cases j <;> rfl
    rw [he]; exact (Set.ext_iff.mp hα (fun _ => s ())).symm
  have reqEval (φ : J.Formula V) (c : K) : test (req φ) c ↔ openDisc O c (O.valuation b) ⊆ A ∧
      ∀ t ∈ openDisc O c (O.valuation b), test φ t ↔ test φ c := by
    simp only [test,req,outer,Formula.realize_inf,Formula.realize_iAlls,Formula.realize_imp,
      Formula.realize_iff,Formula.realize_relabel,ballEval,bodyEval]
    have he (s : Unit → K) : Sum.elim (Sum.elim p (fun _ => c)) s ∘ rebind = Sum.elim p (fun _ => s ()) := by
      funext j; rcases j with j|⟨⟩ <;> rfl
    have ev (s : Unit → K) : (φ.Realize (Sum.elim (Sum.elim p (fun _ => c)) s ∘ rebind) ↔
        φ.Realize (Sum.elim (Sum.elim p (fun _ => c)) s ∘ Sum.inl)) ↔ (test φ (s ()) ↔ test φ c) := by
      rw [he]; rfl
    constructor
    · rintro ⟨a,u⟩; exact ⟨fun t => a (fun _ => t),fun t h => (ev (fun _ => t)).mp (u _ h)⟩
    · rintro ⟨a,u⟩; exact ⟨fun _ h => a h,fun s h => (ev s).mpr (u (s ()) h)⟩
  let D (i : I) := openDisc O (centers i) (O.valuation b)
  have disjoint := fixed_radius_disjoint O centers (O.valuation b) inj
  have convex i : (D i).OrdConnected := valuativeDisc_ordConnected O hO (centers i) (Iio (O.valuation b))
    (fun _ _ h hb => h.trans_lt hb)
  have finite (T : Finset (J.Formula V)) (hT : (T : Set _) ⊆ range req) :
      ∃ c : K, ∀ φ ∈ T, test φ c := by
    rw [←image_univ] at hT
    obtain ⟨H,_,rfl⟩ := Finset.subset_set_image_iff.mp hT
    have small := H.finite_toSet.biUnion (fun φ _ => finite_cutLabels D convex disjoint (hnf φ))
    obtain ⟨i,_,avoid⟩ := (infinite_univ (α := I)).exists_notMem_finite small
    refine ⟨centers i,fun ψ hψ => ?_⟩
    obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hψ
    have cn : centers i ∈ D i := mem_openDisc_center O ((map_ne_zero _).mpr bn) _
    apply (reqEval φ _).mpr
    refine ⟨inside i,fun t ht => ?_⟩
    have forbid : i ∉ cutLabels D {x | test φ x} := fun h => avoid (mem_iUnion₂.mpr ⟨φ,hφ,h⟩)
    exact ⟨fun yes => by_contra (fun no => forbid ⟨⟨t,ht,yes⟩,centers i,cn,no⟩),
      fun yes => by_contra (fun no => forbid ⟨⟨centers i,cn,yes⟩,t,ht,no⟩)⟩
  obtain ⟨c,hc⟩ := sat p (range req) finite
  have good (φ : J.Formula V) := (reqEval φ c).mp (hc _ (mem_range_self φ))
  let B := openDisc O c (O.valuation b)
  let C := openDiscRepresentatives O B (O.valuation b)
  refine ⟨c,(good ⊥).1,?_,⟨c,mem_openDisc_center O ((map_ne_zero _).mpr bn) _⟩,?_⟩
  · let δ : J.Formula (P ⊕ (Unit ⊕ Fin 2)) := discMemberFormula F false (.var (.inr (.inl ()))) (.var (.inr (.inr 0))) (.var (.inr (.inr 1)))
    refine ⟨δ,fun t v hv => ?_⟩
    change t () ∈ openDisc O c (O.valuation b) ↔ _
    rw [←hv.1]
    exact (realize_discMemberFormula O hF false (.var (.inr (.inl ()))) (.var (.inr (.inr 0)))
      (.var (.inr (.inr 1))) (Sum.elim (Subtype.val : P → K) (Sum.elim t v))).symm
  · rintro U ⟨ψ,hψ⟩ x hx y hy
    let renamed : P ⊕ (Unit ⊕ Fin 2) → V := Sum.elim (Sum.inl ∘ Sum.inl)
      (Sum.elim (fun _ => .inr ()) (Fin.cases (.inr ()) (fun _ => .inl (.inr ()))))
    let φ := ψ.relabel renamed
    have trace (a : K) (ha : a ∈ B) : a ∈ U ↔ test φ a := by
      have hrep : ![a,b] ∈ C := ⟨openDisc_change_center O ha,rfl⟩
      have h := hψ (fun _ => a) ![a,b] hrep
      change a ∈ U ↔ (ψ.relabel renamed).Realize (Sum.elim p (fun _ => a))
      rw [Formula.realize_relabel]
      have he : (Sum.elim p (fun _ => a)) ∘ renamed = Sum.elim Subtype.val (Sum.elim (fun _ => a) ![a,b]) := by
        funext j; rcases j with j | j | i
        · rfl
        · rfl
        · fin_cases i <;> rfl
      rw [he]; exact h
    exact (trace x hx).trans (((good φ).2 x hx).trans (((good φ).2 y hy).symm.trans (trace y hy).symm))

end GeneralizedEuler.Section3
