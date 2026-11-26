module

public import Section4.ValuePadding
public import Section4.CommonValueRefinement
import all Section4.ValueStratification
import all Section4.ValueFrames

/-! The degree formula of Lemma 4.14 in the concrete value semiring. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {J : Language} [J.Structure V] {G : Submodule F V}

theorem support_class {n} (h : ValueLanguage (J := J) G) (a : DefinablePiece J G n) :
    pieceClass a.support (support_definable h a) =
      pieceClass a.domain a.definable * eValue G ^ (n - a.rank) := by
  obtain ⟨r,frame,dom,hd,hi⟩ := a
  have le := Fintype.card_le_of_injective frame.free frame.free.injective
  simp only [Fintype.card_fin] at le
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le le
  simpa [IndependentPiece.support] using value_frame_class G h frame dom hd

theorem piece_degree_decomposition {n} (h : ValueLanguage (J := J) G)
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set V).Definable J D))
    (D : Set (Fin n → V)) (hd : (G : Set V).Definable J D) :
    ∃ (l : ℕ) (a : Fin l → DefinablePiece J G n),
      (∀ x, x ∈ D ↔ ∃ i, x ∈ (a i).support) ∧
      Pairwise (fun i j => Disjoint (a i).support (a j).support) ∧
      pieceClass D hd = ∑ i, pieceClass (a i).domain (a i).definable * eValue G ^ (n - (a i).rank) := by
  classical
  obtain ⟨l,a,cover⟩ := stratify_values _ (fun p D i => h.cut p D i) sat D hd
  have disj : Pairwise (fun i j => Disjoint (a i).support (a j).support) := fun i j ne =>
    Set.disjoint_left.mpr fun x hi hj => ne ((cover x).2 i j hi hj)
  have eq : D = ⋃ i, (a i).support := Set.ext fun x => (cover x).1.trans Set.mem_iUnion.symm
  refine ⟨l,a,fun x => (cover x).1,disj,?_⟩
  have add := pieceClass_partition (fun i => (a i).support) (fun i => support_definable h (a i)) disj
  have first : pieceClass D hd = pieceClass (⋃ i, (a i).support)
      (Set.definable_iUnion_of_finite fun i => support_definable h (a i)) := by
    congr 1
  exact (first.trans add).trans (Finset.sum_congr rfl fun i _ => support_class h (a i))

end GeneralizedEuler.Section4.ValueObject
