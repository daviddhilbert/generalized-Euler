module

public import Section3.Monotonicity
public import Section3.ConvexCuts
import all Section2.WeakOminimal
public import Section2.SeparatedSets
public import Section2.ResidueOrder
public import Mathlib.Data.Set.Finite.Lattice

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

/-- A finite union of rectangles with unbounded second projection has
an unbounded section at a single first coordinate. -/
theorem unbounded_section_of_separation {G R : Type*} [LinearOrder R] [Nonempty R]
    {left : Set G → Prop} {right : Set R → Prop} {D : Set (G × R)}
    (sep : SeparatedSets left right D) (unbounded : ¬ BddAbove (Prod.snd '' D)) :
    ∃ g, ¬ BddAbove {r | (g,r) ∈ D} := by
  contrapose! unbounded
  induction sep with
  | empty => simp
  | @insert U V D _ _ _ ih =>
    have ht : BddAbove (Prod.snd '' D) :=
      ih (fun g => (unbounded g).mono (fun _ h => Or.inr h))
    rw [image_union,bddAbove_union]
    refine ⟨?_,ht⟩
    rcases U.eq_empty_or_nonempty with rfl | ⟨g,hg⟩
    · simp
    · exact (unbounded g).mono (fun _ ⟨p,hp,he⟩ => he ▸ Or.inl ⟨hg,hp.2⟩)

/-- In a weakly o-minimal line, an unbounded unary definable set
contains a final segment. -/
theorem tail_of_unbounded_convex_union {X : Type*} [LinearOrder X] [Nonempty X]
    {A : Set X} (h : FiniteConvexUnion A) (hu : ¬ BddAbove A) :
    ∃ x, ∀ y, x < y → y ∈ A := by
  obtain ⟨m,C,hC,rfl⟩ := h
  have hsome : ∃ i, ¬ BddAbove (C i) := by
    by_contra! hb
    exact hu (by simpa using
      (finite_univ.bddAbove_biUnion (S := C)).mpr (fun i _ => hb i))
  obtain ⟨i,hi⟩ := hsome
  obtain ⟨x,hx,_⟩ := not_bddAbove_iff.mp hi (Classical.arbitrary X)
  refine ⟨x,fun y hxy => ?_⟩
  obtain ⟨z,hz,hyz⟩ := not_bddAbove_iff.mp hi y
  exact mem_iUnion.mpr ⟨i,(hC i).out hx hz ⟨hxy.le,hyz.le⟩⟩

set_option linter.style.haveILetI false in
/-- Lemma 3.2 from Section 2 orthogonality and weak o-minimality. Apply
separation to the image of (signed value of the output, residue of the
input). One value occurs at unbounded residues, hence on a tail of O. -/
theorem eventuallyConstantValue_of_separation {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O) (f : O → K)
    (hsep : SeparatedSets (fun _ => True) (fun _ => True)
      (range (fun x : O => (signedValue O hO (rv O (f x)),IsLocalRing.residue O x))))
    (htame : ∀ g, FiniteConvexUnion {x : O | signedValue O hO (rv O (f x)) = g}) :
    EventuallyConstantValue O hO f := by
  letI := residueLinearOrder O hO
  letI := residue_isOrderedRing O hO
  let D := range (fun x : O => (signedValue O hO (rv O (f x)),IsLocalRing.residue O x))
  have hproj : Prod.snd '' D = univ := by
    apply eq_univ_of_forall
    intro r
    obtain ⟨x,hx⟩ := IsLocalRing.residue_surjective r
    exact ⟨_,mem_range_self x,hx⟩
  have hu : ¬ BddAbove (Prod.snd '' D) := by rw [hproj]; exact not_bddAbove_univ
  obtain ⟨g,hg⟩ := unbounded_section_of_separation hsep hu
  have hf : ¬ BddAbove {x : O | signedValue O hO (rv O (f x)) = g} := by
    rintro ⟨b,hb⟩
    apply hg
    refine ⟨IsLocalRing.residue O b,?_⟩
    rintro z ⟨x,he⟩
    rw [←(show IsLocalRing.residue O x = z from congrArg Prod.snd he)]
    exact residue_monotone O hO (hb (congrArg Prod.fst he))
  obtain ⟨b,hb⟩ := tail_of_unbounded_convex_union (htame g) hf
  exact ⟨b,fun x y hx hy => (hb x hx).trans (hb y hy).symm⟩

end GeneralizedEuler.Section3
