module

public import Section4.MixedRectangleSeparation
public import Section4.WholeFiberRelation
import all Section4.FiniteScissors
import all Section2.RVSplitCoordinates

/-! Factor a fixed-base mixed partial matching into finite disjoint
products of definable graphs on value tuples and residue tuples. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} {J JG JH : Language} [J.Structure K] [J.Structure (Residue O)]
  [JG.Structure O.ValueGroupˣ] [JH.Structure (Residue O)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {A : Set O.ValueGroupˣ} {B : Set (Residue O)} {p : F → O.ValueGroupˣ → O.ValueGroupˣ}
  (s : RVValueSection O)
  (prim : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO A B p P)
  (g : F → PositiveField K →* PositiveField K) (power : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (sectionPower : ∀ e γ, P e (s.representative γ) = s.representative (p e γ))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (base : ∀ t : S.carrier .rv, (s.encode t.val).1 ∈ A ∧ (s.encode t.val).2 ∈ B)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x,
      q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

variable {I I' H H' : Type} [Finite I] [Finite I'] [Finite H] [Finite H']

def pairedSet {X : Type*} {M N : Type} (D : Set ((M → X) × (N → X))) :
    Set (M ⊕ N → X) := {w | (w ∘ Sum.inl,w ∘ Sum.inr) ∈ D}

def mixedPair (x : I → Residue O) (a : H → O.ValueGroupˣ) : I ⊕ H → RV0 O :=
  Sum.elim (residueRV O ∘ x) (s.representative ∘ a)

def mixedGraph (U : Set ((I ⊕ H) ⊕ (I' ⊕ H') → RV0 O)) :
    Set (((H → O.ValueGroupˣ) × (H' → O.ValueGroupˣ)) × ((I → Residue O) × (I' → Residue O))) :=
  {z | Sum.elim (mixedPair s z.2.1 z.1.1) (mixedPair s z.2.2 z.1.2) ∈ U}

private theorem packDef {M N : Type} {X : Type*} {L : Language} [L.Structure X] {C : Set X}
      {D : Set (M ⊕ N → X)} (h : C.Definable L D) :
      C.Definable L (pairedSet ((fun z : (M → X) × (N → X) => Sum.elim z.1 z.2) ⁻¹' D)) := by
    convert h using 1
    ext x
    change (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) ∈ D ↔ x ∈ D
    exact (congrArg (· ∈ D) (funext (Sum.rec (fun _ => rfl) (fun _ => rfl)))).to_iff

include prim g power clamp units sectionPower base qe in
theorem mixed_graph_separated (U : Set ((I ⊕ H) ⊕ (I' ⊕ H') → RV0 O)) (hu : isRVSet _ S U) :
    SeparatedSets (fun D => A.Definable JG (pairedSet D)) (fun U => B.Definable JH (pairedSet U)) (mixedGraph s U) := by
  let shuffle : (I ⊕ H) ⊕ (I' ⊕ H') → (I ⊕ I') ⊕ (H ⊕ H') :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
  have sep := mixed_rectangle_separation s prim g power clamp units sectionPower S base qe _
    (isRVSet_precomp shuffle hu)
  have h := SeparatedSets.preimage (left := A.Definable JG) (right := B.Definable JH) (fun z => Sum.elim z.1 z.2) (fun z => Sum.elim z.1 z.2)
    (left' := fun D => A.Definable JG (pairedSet D)) (right' := fun D => B.Definable JH (pairedSet D))
    (fun h => packDef h) (fun h => packDef h) sep
  convert h using 1
  ext z
  apply (congrArg (· ∈ U) _).to_iff
  funext i
  rcases i with (i|i)|(i|i) <;> rfl

include prim g power clamp units sectionPower base qe in
theorem mixed_graph_factors (U : Set ((I ⊕ H) ⊕ (I' ⊕ H') → RV0 O)) (hu : isRVSet _ S U)
    (single : ∀ {a b b' x y y'}, ((a,b),x,y) ∈ mixedGraph s U → ((a,b'),x,y') ∈ mixedGraph s U → b = b' ∧ y = y')
    (inj : ∀ {a a' b x x' y}, ((a,b),x,y) ∈ mixedGraph s U → ((a',b),x',y) ∈ mixedGraph s U → a = a' ∧ x = x') :
    ∃ (n : ℕ) (D : Fin n → Set ((H → O.ValueGroupˣ) × (H' → O.ValueGroupˣ)))
      (R : Fin n → Set ((I → Residue O) × (I' → Residue O))),
      (∀ i, A.Definable JG (pairedSet (D i)) ∧ B.Definable JH (pairedSet (R i))) ∧
      mixedGraph s U = ⋃ i, D i ×ˢ R i ∧
      Pairwise (fun i j => Disjoint (D i ×ˢ R i) (D j ×ˢ R j)) ∧
      ∀ i, ∃ (η : {a // ∃ b, (a,b) ∈ D i} ≃ {b // ∃ a, (a,b) ∈ D i})
        (p : {x // ∃ y, (x,y) ∈ R i} ≃ {y // ∃ x, (x,y) ∈ R i}),
        ∀ a x b y, (a.val,b.val) ∈ D i ∧ (x.val,y.val) ∈ R i ↔ η a = b ∧ p x = y := by
  exact decompose_matching_graph (P := fun D => A.Definable JG (pairedSet D))
    (Q := fun R => B.Definable JH (pairedSet R)) Set.definable_univ (fun h k => h.inter k)
    (fun h => h.compl) Set.definable_empty (fun h k => h.union k) _
    (mixed_graph_separated s prim g power clamp units sectionPower S base qe U hu) single inj

end GeneralizedEuler.Section4
