module

public import Section3.ClosedRayMap
public import Section3.DiscMapPartitions
import all Section3.AtomicShapes
import all Section3.PolydiscImages

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

inductive UnaryForm | point | openDisc | closedDisc | halfThinAnnulus

variable {K : Type*} [Field K] [LinearOrder K] (O : ValuationSubring K)

def HasUnaryForm (A : Set K) : UnaryForm → Prop
  | .point => ∃ a, A = {a}
  | .openDisc => ∃ a r, r ≠ 0 ∧ A = openDisc O a r
  | .closedDisc => ∃ a r, r ≠ 0 ∧ A = closedDisc O a r
  | .halfThinAnnulus => ∃ a r, r ≠ 0 ∧ ∃ b, A = annulusSide b (openDisc O a r) (closedDisc O a r)

theorem hasUnaryForm_of_taxonomy {A : Set K} (h : IsAtomicShape O A) : ∃ k, HasUnaryForm O A k := by
  rcases h with (hp | ⟨a,r,hr,ho | hc⟩) | hh
  · exact ⟨.point,hp⟩
  · exact ⟨.openDisc,a,r,hr,ho⟩
  · exact ⟨.closedDisc,a,r,hr,hc⟩
  · exact ⟨.halfThinAnnulus,hh⟩

variable [DenselyOrdered O.ValueGroup]

private theorem form_open_image {A B : Set K} {f : K → K} (bij : BijOn f A B)
    (shape : IsPointOrOpen O B) (openA : HasUnaryForm O A .openDisc) : HasUnaryForm O B .openDisc := by
  obtain ⟨a,r,hr,rfl⟩ := openA
  rcases shape with ⟨b,rfl⟩ | h
  · obtain ⟨x,hx,y,hy,ne⟩ := openDisc_nontrivial O a hr
    exact (ne (bij.injOn hx hy ((bij.mapsTo hx).trans (bij.mapsTo hy).symm))).elim
  · exact h

/-- Lemma 3.34 from the unary taxonomy, the open-disc image theorem
applied in both directions, and the closed-disc/half-annulus obstruction.
The conclusion gives a common one of the four manuscript forms. -/
theorem atomic_bijection_same_form {A B : Set K} {f g : K → K}
    (bij : BijOn f A B) (inv : InvOn g f A B) (taxA : IsAtomicShape O A) (taxB : IsAtomicShape O B)
    (openF : HasUnaryForm O A .openDisc → IsPointOrOpen O B)
    (openG : HasUnaryForm O B .openDisc → IsPointOrOpen O A)
    (noF : HasUnaryForm O A .closedDisc → HasUnaryForm O B .halfThinAnnulus → False)
    (noG : HasUnaryForm O B .closedDisc → HasUnaryForm O A .halfThinAnnulus → False) :
    ∃ k, HasUnaryForm O A k ∧ HasUnaryForm O B k := by
  have gb : BijOn g B A := by
    have maps : MapsTo g B A := by
      rintro y hy
      obtain ⟨x,hx,rfl⟩ := bij.surjOn hy
      exact (inv.1 hx).symm ▸ hx
    exact ⟨maps,inv.2.injOn,fun x hx => ⟨f x,bij.mapsTo hx,inv.1 hx⟩⟩
  have point {S T : Set K} {h : K → K} (b : BijOn h S T) (p : HasUnaryForm O S .point) :
      HasUnaryForm O T .point := by
    obtain ⟨x,rfl⟩ := p
    exact ⟨h x,b.image_eq.symm.trans image_singleton⟩
  by_cases a : HasUnaryForm O A .point
  · exact ⟨.point,a,point bij a⟩
  by_cases b : HasUnaryForm O B .point
  · exact ⟨.point,point gb b,b⟩
  by_cases o : HasUnaryForm O A .openDisc
  · exact ⟨.openDisc,o,form_open_image O bij (openF o) o⟩
  by_cases p : HasUnaryForm O B .openDisc
  · exact ⟨.openDisc,form_open_image O gb (openG p) p,p⟩
  obtain ⟨i,hi⟩ := hasUnaryForm_of_taxonomy O taxA
  obtain ⟨j,hj⟩ := hasUnaryForm_of_taxonomy O taxB
  cases i <;> cases j <;> first
    | exact (a hi).elim
    | exact (b hj).elim
    | exact (o hi).elim
    | exact (p hj).elim
    | exact (noF hi hj).elim
    | exact (noG hj hi).elim
    | exact ⟨_,hi,hj⟩

end GeneralizedEuler.Section3
