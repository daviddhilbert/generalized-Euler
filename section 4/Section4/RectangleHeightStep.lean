module

public import Section4.RectangleHeightCut
public import Section4.NormalizedRemainderBijection
import all Section4.RectangleHeightCut
import all Section4.NormalizedRemainderBijection
import all Section4.GlobalRectangleMatches
import all Section4.RectanglePairCuts
import all Section4.RectangleFiberFamilies
import all Section4.IndependentRectangleMatches
import all Section4.TaggedFiberMatching
import all Section4.NormalRectangles

/-! One step of the second proof of Proposition 4.21 for whole finite
families. It constructs the lower-height comparison and compares all
removed tensors without additive cancellation. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.NormalRectangle
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {O : ValuationSubring K} [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  {v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ}
  {J JG : Language} [J.Structure K] [J.Structure (Residue O)] [JG.Structure (Additive O.ValueGroupˣ)]
  {hO : IsOrderConvex O} {P : F → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := J) O hO P)}
  {G : Submodule F (Additive O.ValueGroupˣ)} {k : ℕ}
variable {I H : Type} [Fintype I] [Fintype H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S k)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

open scoped TensorProduct
open ValueObject
variable {C R W : Type*} [CommSemiring C] [CommSemiring R] [CommSemiring W] [Algebra C R] [Algebra C W]
  (res : ResidueSemiring (canonicalStructure (L := J) O hO P) S (signedLabel O hO) →+* R)
  (val : SemiringOfSets (J := JG) (G : Set (Additive O.ValueGroupˣ)) →+* W)

variable {height : ℕ}
variable (cuts : ∀ i j, PairCut (C := C) c pull hv s hs d f res val i j height)

variable (graph : ∀ i j, isRVSet _ S (RVFamily.graphPiece _ _ f i j))
  (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
  (units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1)
  (clamp : ∀ e t, ¬ IsPositiveRV O t → P e t = 0)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (base : ∀ t : S.carrier .rv, ((linearValueSection v hv s hs).encode t.val).1 ∈ G)
  (qe : ∀ {N : Type} [Finite N] (φ : SortedFormula J F (FullRVVariables S N)),
    ∃ q : SortedFormula J F (FullRVVariables S N), q.IsQF ∧ ∀ x,
      q.realize (canonicalStructure (L := J) O hO P) x ↔ φ.realize (canonicalStructure (L := J) O hO P) x)

variable (lang : ValueLanguage (J := JG) G) (e : C)
  (resBalance : algebraMap C R e = res (entireUnitWeight O v hv hO P S 1))
  (valBalance : algebraMap C W e = val (eValue (J := JG) G))
  (rep : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (sat : RealizesAffineAvoidance G (fun _ D => (G : Set (Additive O.ValueGroupˣ)).Definable JG D))

include cuts graph agrees units clamp powers base qe lang resBalance valBalance rep sat in
theorem source_height_cut (bound : ∀ i, (c i).r ≤ height) (other : ∀ j, (d j).r ≤ height) (i : I) :
    let a := leftCut c pull hv s hs d f res val cuts i
    ∃ (l : ℕ) (rest : Fin l → Subrectangle (c i))
      (normal : Fin l → NormalRectangle (JG := JG) (G := G) O v hO P S k),
      (∀ t, (normal t).r < height ∧ RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier (rest t).points (normal t).points) ∧
      Pairwise (fun t t' => Disjoint (rest t).labels (rest t').labels) ∧
      ((c i).units ×ˢ (c i).values) \ (⋃ t, (a t).labels) = ⋃ t, (rest t).labels ∧
      (c i).tensor hv res val (C := C) = (∑ t, (a t).rect.tensor hv res val) + ∑ t, (normal t).tensor hv res val := by
  apply cut_to_lower_height O v hv hO P powers S lang e res val resBalance valBalance s hs rep pull sat (c i)
    _ (leftCut_disjoint c pull hv s hs d f res val cuts i) height (bound i)
  intro top
  apply leftCut_coverage c pull hv s hs d f res val cuts i top
  intro a tag ind
  have ha : (c a.1.1).r = height := tag ▸ top
  obtain ⟨b,hb,h⟩ := independent_label_match c pull hv s hs d f graph g agrees units clamp powers base qe a ind
    (fun j => ha.symm ▸ other j)
  exact ⟨b,hb.trans ha,h⟩

include cuts graph agrees units clamp powers base qe lang resBalance valBalance rep sat in
theorem height_step (bound : ∀ i, (c i).r ≤ height) (other : ∀ j, (d j).r ≤ height)
    (lower : ∀ {A B : Type} [Fintype A] [Fintype B]
      (p : A → NormalRectangle (JG := JG) (G := G) O v hO P S k)
      (q : B → NormalRectangle (JG := JG) (G := G) O v hO P S k),
      (∀ i, (p i).r < height) → (∀ j, (q j).r < height) → (rvFamily p pull).Iso (rvFamily q pull) →
      (∑ i, (p i).tensor hv res val (C := C)) = ∑ j, (q j).tensor hv res val) :
    (∑ i, (c i).tensor hv res val (C := C)) = ∑ j, (d j).tensor hv res val := by
  classical
  let flip := flippedCuts c pull hv s hs d f res val cuts
  choose nl L p hl djL remL sumL using source_height_cut c pull hv s hs d f res val cuts graph g agrees units clamp powers
    base qe lang e resBalance valBalance rep sat bound other
  choose nr R' q hr djR remR sumR using source_height_cut d pull hv s hs c f.symm res val flip
    (RVFamily.inverse_graph _ _ f graph) g agrees units clamp powers base qe lang e resBalance valBalance rep sat other bound
  let pp (t : (i : I) × Fin (nl i)) := p t.1 t.2
  let qq (t : (j : H) × Fin (nr j)) := q t.1 t.2
  have iso := normalized_remainder_iso c pull hv s hs d f res val cuts graph L R' djL djR remL remR pp qq
    (fun i t => (hl i t).2) (fun j t => (hr j t).2)
  have rest := lower pp qq (fun t => (hl t.1 t.2).1) (fun t => (hr t.1 t.2).1) iso
  rw [Fintype.sum_sigma,Fintype.sum_sigma] at rest
  simp_rw [sumL,sumR]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  apply congrArg₂ (· + ·) _ rest
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl fun t _ => (cuts i j).weights t

end GeneralizedEuler.Section4.NormalRectangle
