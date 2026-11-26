module

public import Section4.RectangleFiberFamilies
public import Section4.RepresentedFiberMatches
public import Section4.SignedValueReflection
import all Section4.RectangleFiberFamilies
import all Section4.RepresentedFiberMatches
import all Section4.SignedRectangleFactors
import all Section4.NormalRectangles
import all Section4.RVTaggedEquivalence
import all Section4.RectangleClasses
import all Section4.ResidueWeights
import all Section4.CanonicalChartMaps
import all Section4.TaggedFiberMatching
import all Section4.FiniteScissors

/-! The relation of whole matches from the height proof, represented by
RV points over the original base. Its labels consist of the residue tuple
and the values of the free coordinates in a specified rectangle. -/
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

def rawLabel (i : I) (x : Fin (c i).m ⊕ Fin (c i).r → RV0 O) :
    (j : I) × ((Fin (c j).m → RV0 O) × (Fin (c j).r → SignedValueGroup O)) :=
  ⟨i,x ∘ Sum.inl,signedLabel O hO ∘ x ∘ Sum.inr⟩

def pointLabel (x : (rvFamily c pull).Points) := rawLabel c x.1 x.2.val

def labelTest : RVFamily.LabelTest (rvFamily c pull) _ (pointLabel c pull) where
  test i j x y := rawLabel c i x = rawLabel c j y ∧ ∀ n, y (.inr n) ≠ 0
  correct i j x y := ⟨And.left,fun eq => ⟨eq,fun n =>
    (positiveSharp_pos O v _ _ y.property.2 n).ne_zero O⟩⟩
  definable i j := by
    by_cases eq : i = j
    · subst j
      let N := Fin (c i).m ⊕ Fin (c i).r
      let l : Fin (c i).m → N ⊕ N := Sum.inl ∘ Sum.inl
      let r : Fin (c i).m → N ⊕ N := Sum.inr ∘ Sum.inl
      have units : isRVSet _ S {p : N ⊕ N → RV0 O | p ∘ l = p ∘ r} := by
        unfold isRVSet
        convert SortedDefinableOver.iInter (fun j : Fin (c i).m =>
          SortedDefinableOver.coordinate_eq (M := canonicalStructure (L := J) O hO P)
            (A := S.carrier) (Var := RVVariables (N ⊕ N)) .rv (l j) (r j)) using 1
        ext z
        simp [funext_iff]
      let free : Fin (c i).r ⊕ Fin (c i).r → N ⊕ N :=
        Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr)
      have vals := isRVSet_precomp free (signed_label_fiber_relation O hO P S (c i).r)
      refine (show {z : N ⊕ N → RV0 O | rawLabel c i (z ∘ Sum.inl) = rawLabel c i (z ∘ Sum.inr) ∧
          ∀ n, z (.inr (.inr n)) ≠ 0} = _ from ?_).symm ▸ (isRVSet_inter units vals)
      ext z
      change (rawLabel c i (z ∘ Sum.inl) = rawLabel c i (z ∘ Sum.inr) ∧ _) ↔ _ ∧ _ ∧ _
      constructor
      · rintro ⟨same,nz⟩
        have e := (Sigma.mk.inj_iff.mp same).2.eq
        exact ⟨congrArg Prod.fst e,nz,(congrArg Prod.snd e).symm⟩
      · rintro ⟨u,nz,w⟩
        exact ⟨Sigma.ext rfl (heq_of_eq (Prod.ext u w.symm)),nz⟩
    · have empty : {z : (rvFamily c pull).Coord i ⊕ (rvFamily c pull).Coord j → RV0 O |
            rawLabel c i (z ∘ Sum.inl) = rawLabel c j (z ∘ Sum.inr) ∧
            ∀ n, z (.inr (.inr n)) ≠ 0} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun _ e => eq (congrArg Sigma.fst e.1)
      exact empty.symm ▸ (show isRVSet (canonicalStructure (L := J) O hO P) S
          (∅ : Set ((rvFamily c pull).Coord i ⊕ (rvFamily c pull).Coord j → RV0 O)) from
        ⟨.falsum,fun _ => Iff.rfl⟩)

variable (d : H → NormalRectangle (JG := JG) (G := G) O v hO P S l)
    (f : (rvFamily c pull).Points ≃ (rvFamily d pull).Points)
    (graph : ∀ i j, isRVSet _ S (RVFamily.graphPiece _ _ f i j))

include graph in
theorem whole_graph_definable (i : I) (j : H) :
    isRVSet _ S (RVFamily.representedMatches (rvFamily c pull) (rvFamily d pull)
      (a := pointLabel c pull) (b := pointLabel d pull) f i j) :=
  RVFamily.representedMatches_definable _ _ (labelTest c pull) (labelTest d pull) f graph i j

end GeneralizedEuler.Section4.NormalRectangle
