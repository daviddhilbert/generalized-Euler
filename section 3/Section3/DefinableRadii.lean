module

public import Section3.ClosedDiscImages
public import Section2.ValuedFieldFormulas
public import Section2.PowerBounded
import all Section2.PowerBounded

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set
variable {K : Type*} [Field K] {L : Language} [L.Structure K] (O : ValuationSubring K)

/-- A relation on two values is definable in representatives. Naming a
center or a radius is allowed in the value-group decomposition theorem. -/
def valuePairLift (G : Set (O.ValueGroup × O.ValueGroup)) : Set (Fin 2 → K) :=
  {w | (O.valuation (w 0), O.valuation (w 1)) ∈ G}

/-- The radius graph is defined by equality of two discs. The formula
tests every point of the proposed output disc, including all preimages
on the source side. It works for a partial graph on A. -/
theorem definable_image_radius_graph {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (A : Set K) (f : K → K) (a : K) (r : O.ValueGroup) (sub : openDisc O a r ⊆ A)
    (ρ : O.ValueGroup → O.ValueGroup)
    (eqr : ∀ s < r, f '' closedDisc O a s = closedDisc O (f a) (ρ s)) :
    letI := convexStructure O L
    (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph A f) →
    (univ : Set K).Definable (convexLanguage L) (valuePairLift O (fieldGraph (Ioo 0 r) ρ)) := by
  let := convexStructure O L
  rintro ⟨φ,hφ⟩
  obtain ⟨b,hb⟩ := O.valuation_surjective r
  let J := convexLanguage L
  let P : Set K := univ
  let inj := J.lhomWithConstants P
  let con {I : Type} (v : K) : J[[P]].Term I := (J.con (⟨v,mem_univ _⟩ : P)).term
  let C {I : Type} (x : I) (a : K) (s : I) : J[[P]].Formula I := (inj.onFormula
    (discMemberFormula F true (.var (0 : Fin 3)) (.var 1) (.var 2))).subst ![.var x,con a,.var s]
  have memC {I : Type} (x : I) (a : K) (s : I) (v : I → K) :
      (C x a s).Realize v ↔ v x ∈ closedDisc O a (O.valuation (v s)) := by
    change BoundedFormula.Realize (BoundedFormula.subst _ _) _ default ↔ _
    rw [BoundedFormula.realize_subst]
    change (inj.onFormula _).Realize _ ↔ _
    rw [LHom.realize_onFormula,realize_discMemberFormula O hF]
    rfl
  let B := Fin 2 ⊕ Unit
  let D := B ⊕ Unit
  let x : D := .inr ()
  let y : B := .inr ()
  let graph := φ.relabel ![x,Sum.inl y]
  let src := Formula.iExs Unit ((C x a (.inl (.inl 0))) ⊓ graph)
  let tgt := C y (f a) (.inl 1)
  let eqn := Formula.iAlls Unit (src.iff tgt)
  let valLt : J[[P]].Formula (Fin 2) := (inj.onFormula (valuationLEFormula F (.var (0 : Fin 2)) (.var 1))).subst ![con b,.var 0]
  let pos := (Term.var (0 : Fin 2)).equal (con 0)
  refine ⟨pos.not ⊓ valLt.not ⊓ eqn,?_⟩
  ext w
  have rangeCond : (pos.not ⊓ valLt.not).Realize w ↔ O.valuation (w 0) ∈ Ioo 0 r := by
    simp only [Formula.realize_inf,Formula.realize_not]
    have hv : valLt.Realize w ↔ r ≤ O.valuation (w 0) := by
      change BoundedFormula.Realize (BoundedFormula.subst _ _) _ default ↔ _
      rw [BoundedFormula.realize_subst]
      change (inj.onFormula _).Realize _ ↔ _
      rw [LHom.realize_onFormula,realize_valuationLEFormula O hF]
      change O.valuation b ≤ _ ↔ _
      rw [hb]; rfl
    change (w 0 ≠ 0 ∧ ¬ valLt.Realize w) ↔ _
    rw [hv,not_le]
    exact and_congr ((map_ne_zero O.valuation).symm.trans pos_iff_ne_zero.symm) Iff.rfl
  have ge (z : D → K) : graph.Realize z ↔ z x ∈ A ∧ z (.inl y) = f (z x) := by
    rw [Formula.realize_relabel]
    exact (Set.ext_iff.mp hφ _).symm
  have eqtest (hs : O.valuation (w 0) < r) :
      eqn.Realize w ↔ f '' closedDisc O a (O.valuation (w 0)) = closedDisc O (f a) (O.valuation (w 1)) := by
    rw [Set.ext_iff]
    change (Formula.iAlls Unit _).Realize _ ↔ _
    simp only [Formula.realize_iAlls,Formula.realize_iff,src,Formula.realize_iExs,Formula.realize_inf,
      ge,tgt,memC,x,y,Sum.elim_inl,Sum.elim_inr]
    have ins : closedDisc O a (O.valuation (w 0)) ⊆ A :=
      fun z hz => sub ((show O.valuation (z-a) ≤ _ from hz).trans_lt hs)
    constructor
    · intro rule z
      apply Iff.trans _ (rule (fun _ => z))
      exact ⟨fun ⟨k,hk,he⟩ => ⟨fun _ => k,hk,ins hk,he.symm⟩,fun ⟨k,hk,_,he⟩ => ⟨k (),hk,he.symm⟩⟩
    · intro rule z
      apply Iff.trans _ (rule (z ()))
      exact ⟨fun ⟨k,hk,_,he⟩ => ⟨k (),hk,he.symm⟩,fun ⟨k,hk,he⟩ => ⟨fun _ => k,hk,ins hk,he.symm⟩⟩
  change (O.valuation (w 0) ∈ Ioo 0 r ∧ O.valuation (w 1) = ρ (O.valuation (w 0))) ↔ (pos.not ⊓ valLt.not ⊓ eqn).Realize w
  rw [Formula.realize_inf,rangeCond]
  apply and_congr_right
  intro hs
  rw [eqtest hs.2,eqr _ hs.2]
  constructor
  · intro he; rw [he]
  · intro he
    exact le_antisymm ((closedDisc_subset_iff_radius O).mp he.symm.subset)
      ((closedDisc_subset_iff_radius O).mp he.subset)

/-- The one-dimensional piecewise-affine consequence of Theorem B,
stated for arbitrary induced definable graphs in positive values. -/
def ValueAffineDecomposition : Prop :=
  letI := convexStructure O L
  ∀ (r : O.ValueGroup) (ρ : O.ValueGroup → O.ValueGroup),
    (univ : Set K).Definable (convexLanguage L) (valuePairLift O (fieldGraph (Ioo 0 r) ρ)) →
    ∃ n, ∃ C : Fin n → Set O.ValueGroup, Ioo 0 r ⊆ ⋃ j, C j ∧ (∀ j, (C j).OrdConnected) ∧
      ∀ j, AntitoneOn ρ (C j) ∨ ∃ e : O.ValueGroup ≃o O.ValueGroup, ∀ t ∈ C j, ρ t = e t

/-- Corrected converse after Definition 3.23 from one definable graph.
Swapping the coordinates gives the graph for the inverse. -/
theorem definable_discToDisc_of_closed [DenselyOrdered O.ValueGroup] {F : FieldTerms (convexLanguage L)}
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (affine : ValueAffineDecomposition (L := L) O) {A B : Set K} {f g : K → K}
    (bij : BijOn f A B) (inv : InvOn g f A B)
    (fc : PreservesClosedDiscsOn O A f) (gc : PreservesClosedDiscsOn O B g) :
    letI := convexStructure O L
    (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph A f) → DiscToDiscOn O A B f g := by
  let := convexStructure O L
  intro graph
  have inverse : (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph B g) := by
    change (univ : Set K).Definable (convexLanguage L) {w : Fin 2 → K | (w 0,w 1) ∈ fieldGraph B g}
    convert (show (univ : Set K).Definable (convexLanguage L) {w : Fin 2 → K | (w 0,w 1) ∈ fieldGraph A f} from graph).preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
    ext w
    change (w 0 ∈ B ∧ w 1 = g (w 0)) ↔ w 1 ∈ A ∧ w 0 = f (w 1)
    constructor
    · rintro ⟨hy,he⟩; rw [he]; exact ⟨(bij.symm inv.symm).mapsTo hy,(inv.2 hy).symm⟩
    · rintro ⟨hx,he⟩; rw [he]; exact ⟨bij.mapsTo hx,(inv.1 hx).symm⟩
  have terminal {S : Set K} {h : K → K} (dg : (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph S h)) :
      HasTerminalAffineRadius O S h := terminal_radius_of_affine_pieces O
    (fun a r _ sub ρ eqr => affine r ρ (definable_image_radius_graph O hF S h a r sub ρ eqr dg))
  exact discToDisc_of_preservesClosed_both_directions O bij inv fc gc (terminal graph) (terminal inverse)

end GeneralizedEuler.Section3
