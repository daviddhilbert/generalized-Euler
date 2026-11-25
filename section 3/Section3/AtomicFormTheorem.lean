module

public import Section3.IntrinsicAnnulus
public import Section3.FourForms
import all Section3.FourForms
import all Section3.AtomicShapes
import all Section3.DiscMaps
import all Section2.PowerBounded

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
  (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)

structure UnaryMapSymmetry (A : Set K) (f : K → K) where
  fieldMap : K ≃+* K
  ordered : StrictMono fieldMap
  ring : RespectsValuationRing O O fieldMap.toRingHom
  source : fieldMap '' A = A
  commutes : ∀ x ∈ A, fieldMap (f x) = f (fieldMap x)
  residueMap : Residue O ≃[L] Residue O
  compatible : ∀ z, residueMap z = mapResidue O O fieldMap.toRingHom ring z

variable {A B : Set K} {f g : K → K}

omit [IsStrictOrderedRing K] [L.Structure K] in
theorem UnaryMapSymmetry.image_fixed (e : UnaryMapSymmetry (L := L) O A f) :
    e.fieldMap '' (f '' A) = f '' A := by
  calc e.fieldMap '' (f '' A) = (fun x => e.fieldMap (f x)) '' A := image_image ..
       _ = (fun x => f (e.fieldMap x)) '' A := image_congr e.commutes
       _ = f '' (e.fieldMap '' A) := (image_image ..).symm
       _ = _ := congrArg (image f) e.source

private def UnaryMapSymmetry.inverse (e : UnaryMapSymmetry (L := L) O A f) (bij : BijOn f A B) (inv : InvOn g f A B) :
    UnaryMapSymmetry (L := L) O B g where
  fieldMap := e.fieldMap
  ordered := e.ordered
  ring := e.ring
  source := by rw [←bij.image_eq]; exact e.image_fixed O
  commutes := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := bij.surjOn hy
    rw [inv.1 hx,e.commutes x hx,inv.1 (e.source.subset (mem_image_of_mem _ hx))]
  residueMap := e.residueMap
  compatible := e.compatible

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- An old definable partition on an atom has a single piece containing
the whole atom. In particular, the local conclusion of 3.24 applies
globally to the atomic injection. -/
theorem atomic_disc_map_of_partition {I : Type*} {D : Set (Set K)} (atom : GeneratesType D A)
    (C : I → Set K) (sub : ∀ i, C i ⊆ A) (cover : A ⊆ ⋃ i, C i) (defC : ∀ i, C i ∈ D)
    (good : ∀ i, DiscToDiscOn O (C i) (f '' C i) f g) : DiscToDiscOn O A (f '' A) f g := by
  obtain ⟨x,hx⟩ := atom.nonempty
  obtain ⟨i,hi⟩ := mem_iUnion.mp (cover hx)
  have eqn := (sub i).antisymm (fun y hy => (atom.uniform _ (defC i) x hx y hy).mp hi)
  exact eqn ▸ good i

/-- Lemma 3.34. In a homogeneous model, take the base-fixing
symmetries on the source atom. The omitted child, both target parents,
inverse equivariance and transitivity on the image follow in the proof.
The disc-preservation input is the finite partition of 3.24 on the atom. -/
theorem atomic_injection_preserves_form [DenselyOrdered O.ValueGroup] {E I : Type*} (powers : E → RV0 O → RV0 O)
    {F : FieldTerms (convexLanguage L)} (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (induced : HasInducedResidueDefinability (L := L) O (canonicalStructure O hO powers))
    (taxA : IsAtomicShape O A) (taxB : IsAtomicShape O B) (disc : DiscToDiscOn O A B f g)
    (mon : StrictMonoOn f A ∨ StrictAntiOn f A)
    (graph : letI := convexStructure O L; (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph A f))
    (symm : I → UnaryMapSymmetry (L := L) O A f) (trans : ∀ x ∈ A, ∀ y ∈ A, ∃ i, (symm i).fieldMap x = y) :
    letI := residueLinearOrder O hO
    letI := residue_isOrderedRing O hO
    IsOMinimal (K := Residue O) L → IsPowerBounded (K := Residue O) L →
    ∀ {T : OrderedFieldTerms L}, InterpretsOrderedFieldTerms (A := Residue O) T →
      ∃ k, HasUnaryForm O A k ∧ HasUnaryForm O B k := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  let := convexStructure O L
  intro omin power T hT
  have cannot {A B : Set K} {f g : K → K} (d : DiscToDiscOn O A B f g)
      (m : StrictMonoOn f A ∨ StrictAntiOn f A)
      (gr : (univ : Set K).Definable₂ (convexLanguage L) (fieldGraph A f))
      (auts : I → UnaryMapSymmetry (L := L) O A f) (tr : ∀ x ∈ A, ∀ y ∈ A, ∃ i, (auts i).fieldMap x = y)
      (closed : HasUnaryForm O A .closedDisc) (half : HasUnaryForm O B .halfThinAnnulus) : False := by
    obtain ⟨c,r,hr,rfl⟩ := closed
    obtain ⟨a,s,hs,upper,rfl⟩ := half
    obtain ⟨d₀,hd₀⟩ := O.valuation_surjective r
    obtain ⟨b₀,hb₀⟩ := O.valuation_surjective s
    have hd := (valuation_abs O d₀).trans hd₀
    have hb := (valuation_abs O b₀).trans hb₀
    have dp := abs_pos.mpr ((map_ne_zero O.valuation).mp (hd₀.trans_ne hr))
    have bp := abs_pos.mpr ((map_ne_zero O.valuation).mp (hb₀.trans_ne hs))
    have target (i : I) := d.1.image_eq ▸ (auts i).image_fixed O
    let lift (i : I) : MarkedDiscAutomorphism (L := L) O c r a s f := {
      fieldMap := (auts i).fieldMap
      ordered := (auts i).ordered
      ring := (auts i).ring
      sourceDisc := (auts i).source
      targetDisc := invariant_annulus_parent O hO a _ hs hb bp upper _ (auts i).ring (target i)
      omitted := invariant_annulus_child O hO a _ hs hb bp upper _ (auts i).ordered (auts i).ring (target i)
      commutes := (auts i).commutes
      languageMap := (auts i).residueMap
      compatible := (auts i).compatible }
    exact no_definable_closed_disc_to_half O hO powers hF minusOne hm induced hr hd hs hb dp bp upper d m lift
      (fun x y => tr _ x.property _ y.property) gr omin power hT
  have inv := disc.2.1
  have reverse := disc.symm O
  have openMap {A B : Set K} {f g : K → K} (h : DiscToDiscOn O A B f g) :
      HasUnaryForm O A .openDisc → IsPointOrOpen O B := by
    rintro ⟨a,r,hr,rfl⟩
    obtain ⟨b,s,hs,eqn⟩ := h.2.2.1 a r hr Subset.rfl
    exact Or.inr ⟨b,s,hs,h.1.image_eq.symm.trans eqn⟩
  apply atomic_bijection_same_form O disc.1 inv taxA taxB (openMap disc) (openMap reverse) (cannot disc mon graph symm trans)
  refine cannot reverse ?_ ?_ (fun i => (symm i).inverse O disc.1 inv) ?_
  · rcases mon with h | h
    · exact Or.inl (fun x hx y hy hxy => (h.lt_iff_lt (reverse.1.mapsTo hx) (reverse.1.mapsTo hy)).mp (by rwa [inv.2 hx,inv.2 hy]))
    · exact Or.inr (fun x hx y hy hxy => (h.lt_iff_gt (reverse.1.mapsTo hx) (reverse.1.mapsTo hy)).mp (by rwa [inv.2 hx,inv.2 hy]))
  · change (univ : Set K).Definable (convexLanguage L) {v : Fin 2 → K | (v 0,v 1) ∈ fieldGraph B g}
    convert (show (univ : Set K).Definable (convexLanguage L) _ from graph).preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
    ext v
    change (v 0 ∈ B ∧ v 1 = g (v 0)) ↔ (v 1 ∈ A ∧ v 0 = f (v 1))
    constructor
    · rintro ⟨h,eqn⟩
      rw [eqn]; exact ⟨reverse.1.mapsTo h,(inv.2 h).symm⟩
    · rintro ⟨h,eqn⟩
      rw [eqn]; exact ⟨disc.1.mapsTo h,(inv.1 h).symm⟩
  · intro x hx y hy
    obtain ⟨i,hi⟩ := trans _ (reverse.1.mapsTo hx) _ (reverse.1.mapsTo hy)
    exact ⟨i,by change (symm i).fieldMap x = y; rw [←inv.2 hx,(symm i).commutes _ (reverse.1.mapsTo hx),hi,inv.2 hy]⟩

end GeneralizedEuler.Section3
