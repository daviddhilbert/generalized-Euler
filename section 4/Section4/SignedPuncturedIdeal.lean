module

public import Section4.GeometricValuePresentation
import all Section4.TaggedBoxPresentations
import all Section4.SignedValueGeneration
import all Section4.ValueScissors
import all Section4.ValueDescent
import all Section4.ValueEmbedding
import all Section4.DefinableValueFrames
import all Section4.BoundedIntervalScissors

/-! The absolute-value condition defining the punctured maximal ideal has
both signs. Its class is twice the unsigned open-ray class. Reflection of
the value coordinate allows either value-order convention. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject PaddedBox
variable {F V : Type*} [Field F] [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V]
  {G : Submodule F V} {J : Language} [J.Structure V] (L : BoxLanguage (J := J) G)
  {Z : Type} [Fintype Z] {H : Language} [H.Structure (Z × V)] (A : Set (Z × V)) (one : Z)
  (interpret : SignedInterpretation (J := J) (H := H) (G : Set V) A)
local notation "σ" => signedPresentationMap (G := G) A one interpret

def allSigns {k} (D : Set (Fin k → V)) : Set (Fin k → Z × V) := {x | (fun j => (x j).2) ∈ D}

omit [LinearOrder V] [IsOrderedAddMonoid V] [Fintype Z] in
include interpret in
theorem allSigns_definable {k} (D : Set (Fin k → V)) (hd : (G : Set V).Definable J D) :
    A.Definable H (allSigns D) := (interpret _).mpr (fun _ => hd)

omit [LinearOrder V] [IsOrderedAddMonoid V] in
theorem allSigns_unary_class (D : Set (Fin 1 → V)) (hd : (G : Set V).Definable J D) :
    pieceClass _ (allSigns_definable A interpret D hd) = (Fintype.card Z) • σ (pieceClass D hd) := by
  rw [signed_piece_decomposition (G : Set V) A one interpret]
  have term (b : Fin 1 → Z) : pieceClass (signInsert (fun _ => one) '' (signInsert b ⁻¹' allSigns D))
      (signed_stratum_definable (G : Set V) A interpret _ _ ((interpret _).mp (allSigns_definable A interpret D hd) b)) =
      σ (pieceClass D hd) := by
    symm
    change σ (pieceClass D hd) = pieceClass (signInsert (fun _ => one) '' D) _
    exact PieceMeasure.descend_piece _ _ _
  simp only [term,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_one]

def lowerRay : Set (Fin 1 → V) := {x | x 0<0}

include L in
theorem lowerRay_class : ∃ hd : (G : Set V).Definable J lowerRay, pieceClass _ hd = pieceClass _ L.ray := by
  let f (x : Fin 1 → V) (j : Fin 1) := -x j
  have df : (G : Set V).DefinableMap J f := by
    intro j
    simpa [f] using (L.arithmetic.smul (-1)).comp (g := fun (x : Fin 1 → V) (_ : Unit) => x j) (fun _ => Set.DefinableFun.proj J)
  have img : f '' upperRay 0 = lowerRay (V := V) := by
    ext y
    exact ⟨fun ⟨x,hx,eq⟩ => eq ▸ (neg_neg_of_pos hx),fun hy => ⟨-y,neg_pos.mpr hy,funext (fun j => neg_neg _)⟩⟩
  have hd : (G : Set V).Definable J lowerRay := img ▸ image_of_map f df _ L.ray
  refine ⟨hd,?_⟩
  have eq := pieceClass_images f id df (fun _ => Set.DefinableFun.proj J) _ L.ray
    (fun x _ y _ eq => funext fun j => neg_inj.mp (congrFun eq j)) Function.injective_id.injOn
  simpa only [img,Set.image_id] using eq

theorem punctured_value_class (two : Fintype.card Z=2) :
    ∃ hd : A.Definable H (allSigns (lowerRay (V := V))),
      pieceClass _ hd = σ (pieceClass _ L.ray) + σ (pieceClass _ L.ray) := by
  obtain ⟨hd,eq⟩ := lowerRay_class L
  exact ⟨_,by rw [allSigns_unary_class A one interpret _ hd,two,two_nsmul,eq]⟩

end GeneralizedEuler.Section4
