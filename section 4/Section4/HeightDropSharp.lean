module

public import Section4.NormalRectangleCover
public import Section4.ValueDegrees
import all Section4.NormalRectangleCover
import all Section4.CanonicalChartMaps
import all Section4.RectangleClasses
import all Section4.PositiveRectangles
import all Section4.ResidueWeights
import all Section4.NormalRectangles
import all Section4.ValueStratification

/-! On an affine value frame, all eliminated coordinates of a sharp
set become unrestricted positive units. The coordinate maps and their
graphs are defined over the original base. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
private theorem frame_lift_image {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
    (v : T →ₗ[F] V) (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) {G : Submodule F V}
    {n r : ℕ} (A : ValueFrame G r n) (D : Set (Fin r → V)) :
    (fun w => A.assemble v s w.1 w.2) '' ({z : Fin r → T | v ∘ z ∈ D} ×ˢ (Set.univ : Set (A.dependent → v.ker))) =
      {x : Fin n → T | v ∘ x ∈ A.eval '' D} := by
  ext x
  constructor
  · rintro ⟨⟨z,b⟩,⟨hz,_⟩,rfl⟩
    exact ⟨v ∘ z,hz,(A.assemble_value v s hs z b).symm⟩
  · rintro ⟨a,ha,eq⟩
    have free : v ∘ (x ∘ A.free) = a := by
      change (v ∘ x) ∘ A.free = a
      rw [← eq,A.project_eval]
    have frame : v ∘ x = A.eval ((v ∘ x) ∘ A.free) := by
      change v ∘ x = A.eval (v ∘ (x ∘ A.free))
      rw [free]
      exact eq.symm
    exact ⟨(x ∘ A.free,A.normalize v s hs x frame),⟨show v ∘ (x ∘ A.free) ∈ D from free.symm ▸ ha,Set.mem_univ _⟩,A.assemble_normalize v s hs x frame⟩

variable {F K : Type*} [Field F] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  {J : Language} [J.Structure K] [J.Structure (Residue O)] (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] {G : Submodule F (Additive O.ValueGroupˣ)}
variable (lang : ValueLanguage (J := JG) G)
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (base : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))

include powers hs base pull lang in
set_option maxHeartbeats 1250000 in
theorem frame_sharp_equivalent {n r : ℕ} (p : DefinablePiece JG G n)
    (idx : Fin r ≃ p.frame.dependent) :
    RVDefinablyEquivalent (canonicalStructure (L := J) O hO P) S.carrier
      (positiveSharp O v p.support) (productSet (unitSet O v (Equiv.refl (Fin r)) Set.univ) (positiveSharp O v p.domain)) := by
  let A := p.frame
  let W := {z : Fin p.rank → Additive (PositiveRV O) | v ∘ z ∈ p.domain} ×ˢ (Set.univ : Set (A.dependent → v.ker))
  have image : (fun w => codeTuple O (A.assemble v s w.1 w.2)) '' W = positiveSharp O v p.support := by
    have eq := congrArg (fun X : Set (Fin n → Additive (PositiveRV O)) => codeTuple O '' X)
      (frame_lift_image v s hs A p.domain)
    rw [Set.image_image] at eq
    exact eq
  have iso := chart_definably_equivalent O P powers v s A idx hO S W (fun i => base (A.shift i))
    (image.symm ▸ pull (support_definable lang p))
  rw [image] at iso
  have target := rectangle_image O v A idx {z | v ∘ z ∈ p.domain} Set.univ
  change codeRectangle O v A idx '' W = productSet (codedResidues O v A idx Set.univ) (positiveSharp O v p.domain) at target
  rw [target,← standard_coded_residues] at iso
  exact iso

end GeneralizedEuler.Section4
