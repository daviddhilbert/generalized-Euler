module

public import Section4.ValueDegrees
public import Section4.RefinedChartTest
import all Section4.ValueScissors
import all Section4.ValuePadding
import all Section4.ValueStratification

public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {J : Language} [J.Structure V]
  {G : Submodule F V} {n r k : ℕ} (lang : ValueLanguage (J := J) G)
  (A : ValueFrame G r n) (B : ValueFrame G k n)

include lang in
theorem projected_value_definable : (G : Set V).DefinableMap J (fun z => B.eval z ∘ A.free) :=
  fun i => lang.frame B (A.free i)

theorem projected_value_injective (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) : Function.Injective (fun z => B.eval z ∘ A.free) := by
  intro x y eq
  apply B.injective
  exact (A.refinement_hull B α hi h x).symm.trans ((congrArg A.eval eq).trans (A.refinement_hull B α hi h y))

theorem projected_value_class (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) (D : Set (Fin k → V)) (hd : (G : Set V).Definable J D) :
    pieceClass ((fun z => B.eval z ∘ A.free) '' D) (image_of_map _ (projected_value_definable lang A B) _ hd) =
      pieceClass D hd * eValue G ^ (r-k) := by
  have general {a b c} (f : (Fin a → V) → (Fin c → V)) (hf : (G : Set V).DefinableMap J f)
      (inj : Function.Injective f) (d : Set (Fin a → V)) (defD : (G : Set V).Definable J d) (eq : a+b=c) :
      pieceClass (f '' d) (image_of_map _ hf d defD) = pieceClass d defD * eValue G ^ b := by
    subst c
    have left := pieceClass_images f (padValues b) hf (pad_definable G) d defD inj.injOn pad_injective.injOn
    have right := (pieceClass_product defD (zeroTuple_definable (J := J) G b)).trans
      (congrArg (pieceClass d defD * ·) (point_power G b))
    exact left.trans ((class_congr G (pad_image d) _ _).trans right)
  exact general _ (projected_value_definable lang A B) (projected_value_injective A B α hi h) D hd (Nat.add_sub_of_le (A.refinement_rank B α hi h))

end GeneralizedEuler.Section4.ValueObject
