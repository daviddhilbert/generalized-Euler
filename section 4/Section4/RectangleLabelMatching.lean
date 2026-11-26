module

public import Section4.IndependentRectangleMatches
import all Section4.IndependentRectangleMatches
import all Section4.WholeMatchRectangles
import all Section4.RectangleFiberFamilies
import all Section4.RectangleMatchGraph
import all Section4.MixedMatchFactors
import all Section4.RepresentedFiberMatches
import all Section4.TaggedFiberMatching
import all Section4.NormalRectangles

/-! The separated relation, read on actual residue and value labels,
is exactly whole-fiber matching. This identifies matching across
different target tags as a single partial bijection. -/
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
  {G : Submodule F (Additive O.ValueGroupˣ)} {k l : ℕ}
variable {I H : Type} [Finite I] [Finite H] (c : I → (NormalRectangle (JG := JG) (G := G) O v hO P S) k)
  (pull : ∀ {r} {D : Set (Fin r → (Additive O.ValueGroupˣ))}, (G : Set (Additive O.ValueGroupˣ)).Definable JG D → isRVSet (canonicalStructure (L := J) O hO P) S (positiveSharp O v D))

variable (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
    (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S l)
  (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)

def keyMatch (a : (fiberFamily c).Label) (b : (fiberFamily d).Label) : Prop :=
  ((Additive.toMul ∘ a.2.val,Additive.toMul ∘ b.2.val),kernelResidue v ∘ a.1.2.val,kernelResidue v ∘ b.1.2.val) ∈
    labelMatching c pull (linearValueSection v hv s hs) d f a.1.1 b.1.1

theorem keyMatch_iff (a : (fiberFamily c).Label) (b : (fiberFamily d).Label) :
    keyMatch c pull hv s hs d f a b ↔ WholeMatch ((fiberFamily c).label (T := Additive (PositiveRV O)) v)
      ((fiberFamily d).label (T := Additive (PositiveRV O)) v) (onFibers c pull d f) a b := by
  let x := sectionLift c s hs a
  let y := sectionLift d s hs b
  let e := onFibers c pull d f
  let A := fiberEquiv c pull
  let B := fiberEquiv d pull
  have eq (t) : f (A t) = B (e t) := (B.apply_symm_apply _).symm
  have rep : keyMatch c pull hv s hs d f a b ↔
      WholeMatch (pointLabel c pull) (pointLabel d pull) f (pointLabel c pull (A x)) (pointLabel d pull (B y)) := by
    change Sum.elim _ _ ∈ RVFamily.representedMatches _ _ _ _ _ ↔ _
    rw [← sectionLift_tuple c hv s hs a,← sectionLift_tuple d hv s hs b,RVFamily.mem_representedMatches]
    exact ⟨fun ⟨_,_,h⟩ => h,fun h => ⟨(A x).2.property,(B y).2.property,h⟩⟩
  rw [rep,wholeMatch_iff,wholeMatch_iff]
  have test (t) : (pointLabel c pull (A t) = pointLabel c pull (A x) ↔ pointLabel d pull (f (A t)) = pointLabel d pull (B y)) ↔
      ((fiberFamily c).label (T := Additive (PositiveRV O)) v t = a ↔
       (fiberFamily d).label (T := Additive (PositiveRV O)) v (e t) = b) := by
    rw [eq]
    change (pointLabel c pull (fiberEquiv c pull t) = pointLabel c pull (fiberEquiv c pull x) ↔
        pointLabel d pull (fiberEquiv d pull (e t)) = pointLabel d pull (fiberEquiv d pull y)) ↔ _
    rw [label_pack c pull hv,label_pack c pull hv,label_pack d pull hv,label_pack d pull hv,
      (encodeFiberLabel_injective c).eq_iff,(encodeFiberLabel_injective d).eq_iff,
      sectionLift_label,sectionLift_label]
  constructor
  · exact fun h t => (test t).mp (h (A t))
  · intro h z
    obtain ⟨t,rfl⟩ := A.surjective z
    exact (test t).mpr (h t)

theorem keyMatch_single {a b b'} (h : keyMatch c pull hv s hs d f a b) (h' : keyMatch c pull hv s hs d f a b') :
    b = b' := by
  let e := onFibers c pull d f
  let x := sectionLift c s hs a
  have label := sectionLift_label c s hs a
  have atX b (h : keyMatch c pull hv s hs d f a b) :
      (fiberFamily d).label (T := Additive (PositiveRV O)) v (e x) = b :=
    ((wholeMatch_iff _ _ _ _ _).mp ((keyMatch_iff c pull hv s hs d f a b).mp h) x).mp label
  exact (atX b h).symm.trans (atX b' h')

theorem keyMatch_inverse (a : (fiberFamily c).Label) (b : (fiberFamily d).Label) :
    keyMatch d pull hv s hs c f.symm b a ↔ keyMatch c pull hv s hs d f a b :=
  labelMatching_inverse c pull _ d f _ _ _ _ _ _

end GeneralizedEuler.Section4.NormalRectangle
