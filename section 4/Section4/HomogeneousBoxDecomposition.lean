module

public import Section4.SemilinearBoxDecomposition
public import Section4.HomogeneousValueLift
import all Section4.HomogeneousValueLift
import all Section4.TaggedBoxPresentations
import all Section4.ValueScissors

/-! Box presentations for the entire homogeneous additive monoid,
including arbitrary signs, tags, and the zero class. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.PaddedBox
open FirstOrder ValueObject Polyhedral
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {G : Submodule F V} {J : Language} [J.Structure V] (L : BoxLanguage (J := J) G)
  (order : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
  {Z : Type} [Fintype Z] {H : Language} [H.Structure (Z × V)] (A : Set (Z × V)) (one : Z)
  (interpret : SignedInterpretation (J := J) (H := H) (G : Set V) A) {k : ℕ}
  (semi : ∀ D : Set (Fin k → V), (G : Set V).Definable J D → SemilinearOver G D)

include order semi in
theorem homogeneous_box_presentation (x : homogeneousValue (J := H) A k) :
    ∃ p : Presentation G k, signedPresentationMap (G := G) A one interpret (presentationValue L p) = x.val := by
  classical
  let σ := signedPresentationMap (G := G) A one interpret
  let T : AddSubmonoid (SemiringOfSets (J := H) A) := {
    carrier := {y | ∃ p : Presentation G k, σ (presentationValue L p) = y}
    zero_mem' := by
      obtain ⟨q,eq⟩ := sum_presentations L (I := Fin 0) (Fin.elim0 : Fin 0 → Presentation G k)
      exact ⟨q,by simp [eq]⟩
    add_mem' := by
      rintro _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
      obtain ⟨q,eq⟩ := sum_presentations L (fun i : Fin 2 => ![u,v] i)
      exact ⟨q,by simp [eq,Fin.sum_univ_two]⟩ }
  have sub : homogeneousValue (J := H) A k ≤ T := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨D,hd,rfl⟩
    exact present_tagged L A one interpret (single D hd) (fun E he => semilinear_box_presentation L order E he (semi E he))
  exact sub x.property

end GeneralizedEuler.Section4.PaddedBox
