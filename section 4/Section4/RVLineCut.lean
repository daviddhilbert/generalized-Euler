module

public import Section4.ValuePointCardinality
public import Section4.FiniteScissors
import all Section4.FiniteScissors
import all Section4.Scissors
import all Section4.Objects
import all Section2.RVDefinableEquivalence

/-! Two disjoint definable self-embeddings give a positive scissor
identity within the original ambient degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}

def homogeneousRV (M : SortedStructure L F Z) (S : SortedSubstructure M) (k : ℕ) : AddSubmonoid (RVSemiring M S) :=
  AddSubmonoid.closure (Set.range fun U : RVObject M S k => objectClass M S ⟨k,U⟩)

def homogeneousRVClass {k} (U : RVObject M S k) : homogeneousRV M S k :=
  ⟨objectClass M S ⟨k,U⟩,AddSubmonoid.subset_closure ⟨U,rfl⟩⟩

theorem homogeneous_self_embeddings {k} (U : RVObject M S k)
    (f g : U.carrier → Fin U.arity → Z .rv) (hf : Function.Injective f) (hg : Function.Injective g)
    (gf : SortedDefinableOver M S.carrier (rvGraph f)) (gg : SortedDefinableOver M S.carrier (rvGraph g))
    (sf : Set.range f ⊆ U.carrier) (sg : Set.range g ⊆ U.carrier) (disj : Disjoint (Set.range f) (Set.range g)) :
    ∃ remainder : RVObject M S k,
      homogeneousRVClass U = homogeneousRVClass U + homogeneousRVClass U + homogeneousRVClass remainder := by
  let B := Set.range f
  let C := Set.range g
  let rest := U.carrier \ (B ∪ C)
  have df : isRVSet M S B := definable_range_of_rvGraph f gf
  have dg : isRVSet M S C := definable_range_of_rvGraph g gg
  have dr : isRVSet M S rest := U.definable.inter (df.union dg).compl
  let R := U.restrict (Set.sdiff_subset : rest ⊆ U.carrier) dr
  have ef : RVDefinablyEquivalent M S.carrier B U.carrier :=
    RVDefinablyEquivalent.symm ⟨Equiv.ofInjective f hf,gf⟩
  have eg : RVDefinablyEquivalent M S.carrier C U.carrier :=
    RVDefinablyEquivalent.symm ⟨Equiv.ofInjective g hg,gg⟩
  let P := U.restrict (Set.union_subset sf sg) (df.union dg)
  have cutBC : objectClass M S ⟨k,P⟩ = objectClass M S ⟨k,U⟩ + objectClass M S ⟨k,U⟩ :=
    scissors_sound M S (RVRelation.cut P U U B C df dg disj rfl ef eg)
  have cutRest : objectClass M S ⟨k,U⟩ = objectClass M S ⟨k,P⟩ + objectClass M S ⟨k,R⟩ := by
    apply scissors_sound M S
    apply RVRelation.cut U P R (B ∪ C) rest (df.union dg) dr Set.disjoint_sdiff_right
      (Set.union_sdiff_cancel (Set.union_subset sf sg))
    · exact ⟨Equiv.refl _,definable_identity_label M S (df.union dg)⟩
    · exact ⟨Equiv.refl _,definable_identity_label M S dr⟩
  exact ⟨R,Subtype.ext (cutRest.trans (congrArg (· + objectClass M S ⟨k,R⟩) cutBC))⟩

end GeneralizedEuler.Section4
