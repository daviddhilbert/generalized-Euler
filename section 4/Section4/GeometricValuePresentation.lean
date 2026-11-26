module

public import Section4.HomogeneousBoxDecomposition
public import Section4.GradedEulerMaps
public import Section4.ValuePresentation
public import Section4.RaySquareScissors
import all Section4.SemiringGroupification
import all Section4.ValueScissors
import all Section4.ArbitraryBoxUnions
import all Section4.TaggedBoxPresentations
import all Section4.ValueBoxProducts
import all Section4.ValueEmbedding
import all Section4.ValueDescent
import all Section4.SignedValueGeneration
import all Section4.Factors

/-! The point and the open ray generate the actual groupified value
semiring. The two graded Euler maps give its polynomial coordinates. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
set_option maxHeartbeats 1600000
open FirstOrder ValueObject PaddedBox Polyhedral SemiringGroupification

private theorem valueRing_generated {W : Type*} {H : Language} [H.Structure W] (A : Set W)
    (T : Subring (SemiringGroupification.Ring (SemiringOfSets (J := H) A)))
    (gen : ∀ {k} (U : Over (J := H) A k), of _ (taggedValueClass A U) ∈ T) :
    ∀ x, x∈T := by
  let R := SemiringOfSets (J := H) A
  let q := (ringConGen (ValueObject.Relation (J := H) A)).mk'
  have pos (x : R) : of R x ∈ T := by
    obtain ⟨p,rfl⟩ := (ringConGen (ValueObject.Relation (J := H) A)).mk'_surjective x
    change ((of R).comp q) p ∈ T
    induction p using MvPolynomial.induction_on with
    | C n =>
      rw [show MvPolynomial.C n = (n : MvPolynomial _ ℕ) from map_natCast _ n,map_natCast]
      simp
    | add _ _ hl hr => rw [map_add]; exact T.add_mem hl hr
    | mul_X _ i h => rw [map_mul]; exact T.mul_mem h (gen i.2)
  intro x
  obtain ⟨p,rfl⟩ := (ringConGen (SemiringGroupification.Relation R)).mk'_surjective x
  induction p using MvPolynomial.induction_on with
  | C z =>
    rw [show MvPolynomial.C z = (z : MvPolynomial R ℤ) from map_intCast _ z,map_intCast]
    simp
  | add _ _ hl hr => rw [map_add]; exact T.add_mem hl hr
  | mul_X _ i h => rw [map_mul]; exact T.mul_mem h (pos i)

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {G : Submodule F V} {J : Language} [J.Structure V] (L : BoxLanguage (J := J) G)
  (order : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
  {Z : Type} [Fintype Z] {H : Language} [H.Structure (Z × V)] (A : Set (Z × V)) (one : Z)
  (interpret : SignedInterpretation (J := J) (H := H) (G : Set V) A)
  (semi : ∀ {k} (D : Set (Fin k → V)), (G : Set V).Definable J D → SemilinearOver G D)

local notation "σ" => signedPresentationMap (G := G) A one interpret
local notation "μ" => RingHom.comp (of (SemiringOfSets (J := H) A)) σ
local notation "pt" => μ (pieceClass _ L.point)
local notation "hray" => μ (pieceClass _ L.ray)

include order semi in
theorem geometric_value_normal (x : SemiringGroupification.Ring (SemiringOfSets (J := H) A)) : x ∈ cellPolynomials pt hray := by
  have rel : hray^2 = -(pt*hray) := by
    have cut := congrArg μ (ray_square_scissors G L.arithmetic L.ray L.point)
    simp only [map_pow,map_add,map_mul] at cut
    linear_combination -cut
  obtain ⟨T,hT,hp,hr⟩ := cellPolynomials_subring pt hray rel
  rw [← hT]
  apply valueRing_generated A T _ x
  intro k U
  obtain ⟨D,eq⟩ := present_tagged L A one interpret U (fun S hs => semilinear_box_presentation L order S hs (semi S hs))
  rw [← eq]
  change μ (presentationValue L D) ∈ T
  unfold presentationValue
  rw [map_sum]
  apply T.sum_mem
  intro i _
  rw [coordinateBox_class (G : Set V) _ (fun j => unary_definable L (D.axes i j) (fun b h => (D.widths i j b h).1)),map_prod]
  apply T.prod_mem
  intro j _
  have side_mem (side : BoxSide V) (hd : (G : Set V).Definable J (unarySide side))
      (width : ∀ a, side = .bounded a → a∈G ∧ 0<a) : μ (pieceClass _ hd) ∈ T := by
    cases side with
    | point => exact hp
    | ray => exact hr
    | bounded t =>
      obtain ⟨old,pos⟩ := width t rfl
      have eq := congrArg (SemiringGroupification.map σ) (bounded_interval_group_class G L.arithmetic t old pos (L.intervals t old) L.ray L.point)
      simp only [map_of,map_neg] at eq
      rw [show μ (pieceClass _ hd) = -pt from eq]
      exact T.neg_mem hp
  exact side_mem _ _ (D.widths i j)

variable (geometric bounded : SemiringOfSets (J := H) A →+* ℤ)
  (gp : geometric ((signedPresentationMap (G := G) A one interpret) (pieceClass _ L.point))=1) (gr : geometric ((signedPresentationMap (G := G) A one interpret) (pieceClass _ L.ray))= -1)
  (bp : bounded ((signedPresentationMap (G := G) A one interpret) (pieceClass _ L.point))=1) (br : bounded ((signedPresentationMap (G := G) A one interpret) (pieceClass _ L.ray))=0)

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] [Fintype Z] in
theorem unsigned_graded (f : SemiringOfSets (J := H) A →+* ℤ) {k} (D : Set (Fin k → V))
    (hd : (G : Set V).Definable J D) :
    GradedEuler.value A f (μ (pieceClass D hd)) = Polynomial.C (f (σ (pieceClass D hd))) * Polynomial.X^k := by
  let B := signInsert (fun _ : Fin k => one) '' D
  have hB := signed_stratum_definable (G : Set V) A interpret (fun _ : Fin k => one) D hd
  have sc : σ (pieceClass D hd)=pieceClass B hB := PieceMeasure.descend_piece _ _ _
  change GradedEuler.value A f (of _ (σ (pieceClass D hd))) = _
  rw [sc]
  exact GradedEuler.value_class A f (single B hB)

include order semi gp gr bp br in
def geometric_value_presentation : SemiringGroupification.Ring (SemiringOfSets (J := H) A) ≃+* valueRing :=
  valuePresentationOfNormal pt hray (GradedEuler.value A geometric) (GradedEuler.value A bounded)
    (by rw [unsigned_graded,gp]; simp)
    (by rw [unsigned_graded,bp]; simp)
    (by rw [unsigned_graded,gr]; simp)
    (by rw [unsigned_graded,br]; simp)
    (geometric_value_normal L order A one interpret @semi)

theorem geometric_value_coordinates (x : SemiringGroupification.Ring (SemiringOfSets (J := H) A)) :
    (geometric_value_presentation L order A one interpret @semi geometric bounded gp gr bp br x).val =
      (GradedEuler.value A geometric x,GradedEuler.value A bounded x) := by
  unfold geometric_value_presentation
  apply valuePresentationOfNormal_apply

theorem geometric_value_ray :
    geometric_value_presentation L order A one interpret @semi geometric bounded gp gr bp br hray = ray := by
  apply Subtype.ext
  rw [geometric_value_coordinates]
  change (_,_) = (-Polynomial.X,0)
  rw [unsigned_graded,unsigned_graded,gr,br]
  simp

end GeneralizedEuler.Section4
