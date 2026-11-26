module

public import Section4.PositiveRectangles
public import Section4.FixedBasePartitions
import all Section4.CellProducts
import all Section4.PositiveRectangles
import all Section4.ValueStratification

/-! A finite disjoint rectangle decomposition for any shear-invariant positive
RV set whose pullback to split coordinates is residue–value separated. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T]
  [AddCommGroup V] [Module F V] (v : T →ₗ[F] V) (s : V →ₗ[F] T)
  (hs : v.comp s = LinearMap.id) (G : Submodule F V)
  (P : ∀ n, Set (Fin n → V) → Prop) {n : ℕ} (Q : Set (Fin n → v.ker) → Prop)

structure PositivePiece where
  value : IndependentPiece P G n
  residueTest : Set (Fin n → v.ker)
  residueDefinable : Q residueTest

namespace PositivePiece
variable {v s hs G P Q}
def residues (p : PositivePiece v G P Q) :=
  {b | p.value.frame.extendResidues v b ∈ p.residueTest}

def carrier (p : PositivePiece v G P Q) (U : Set (Fin n → T)) :=
  {x ∈ U | v ∘ x ∈ p.value.support}

abbrev rectangle (p : PositivePiece v G P Q) :=
  {z : Fin p.value.rank → T // v ∘ z ∈ p.value.domain} × p.residues
end PositivePiece

include hs in
theorem decompose_positive_set (U : Set (Fin n → T))
    (invariant : ∀ L x, x ∈ U → shear v G L ∘ x ∈ U)
    (separated : SeparatedSets (P n) Q
      {p : (Fin n → V) × (Fin n → v.ker) | (fun i => s (p.1 i) + (p.2 i).val) ∈ U})
    (pu : P n Set.univ) (pi : ∀ {a b}, P n a → P n b → P n (a ∩ b))
    (pc : ∀ {a}, P n a → P n aᶜ) (qe : Q ∅) (qu : ∀ {a b}, Q a → Q b → Q (a ∪ b))
    (cut : ∀ {m l} (p : Fin l → ValuePivot G m) (D) (i), P _ D → P _ (firstPivot p D i))
    (sat : RealizesAffineAvoidance G P) :
    ∃ (l : ℕ) (p : Fin l → PositivePiece v G P Q),
      (∀ x, x ∈ U ↔ ∃ i, x ∈ (p i).carrier U) ∧
      Pairwise (fun i j => Disjoint ((p i).carrier U) ((p j).carrier U)) ∧
      (∀ γ, ∃! i, γ ∈ (p i).value.support) ∧
      ∀ i, ∃ e : (p i).rectangle ≃ (p i).carrier U, ∀ z,
        (e z).val = (p i).value.frame.assemble v s z.1.val z.2.val := by
  classical
  obtain ⟨k,D,R,hDR,unique,test⟩ := separated_partition pu pi pc qe qu separated
  choose count a cover using fun i => stratify_values P cut sat (D i) (hDR i).1
  let I := Σ i, Fin (count i)
  let idx := (Fintype.equivFin I).symm
  let piece (i : I) : PositivePiece v G P Q := ⟨a i.1 i.2,R i.1,(hDR i.1).2⟩
  have orig (i : I) (γ) (h : γ ∈ (piece i).value.support) : γ ∈ D i.1 :=
    ((cover i.1 γ).1).mpr ⟨i.2,h⟩
  have supports (γ : Fin n → V) : ∃! j, γ ∈ (piece (idx j)).value.support := by
    obtain ⟨i,hi,only⟩ := unique γ
    obtain ⟨j,hj⟩ := (cover i γ).1.mp hi
    refine ⟨idx.symm ⟨i,j⟩,by change γ ∈ (piece (idx (idx.symm ⟨i,j⟩))).value.support; rw [Equiv.apply_symm_apply]; exact hj,?_⟩
    intro t ht
    apply idx.injective
    rw [Equiv.apply_symm_apply]
    obtain ⟨i',u,eq⟩ : ∃ i' u, idx t = ⟨i',u⟩ := ⟨_,_,rfl⟩
    have same := only _ (orig (idx t) _ ht)
    rw [eq] at same ht ⊢
    change i' = i at same
    subst i'
    exact congrArg (Sigma.mk i) ((cover i γ).2 _ _ ht hj)
  refine ⟨_,piece ∘ idx,?_,?_,supports,?_⟩
  · intro x
    exact ⟨fun hx => ⟨_,hx,(supports (v ∘ x)).choose_spec.1⟩,fun ⟨_,hx⟩ => hx.1⟩
  · intro i j hn
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hn ((supports (v ∘ x)).unique hi.2 hj.2)
  · intro j
    let i := idx j
    let b := a i.1 i.2
    obtain ⟨α,hα,ind⟩ := b.independent
    have localTest (x : Fin n → T) (hx : v ∘ x ∈ b.support) :
        x ∈ U ↔ splitUnit v s hs ∘ x ∈ R i.1 := by
      have h := test (v ∘ x) (splitUnit v s hs ∘ x) i.1 (orig i _ hx)
      have recon : (fun k => s (v (x k)) + (splitUnit v s hs (x k)).val) = x := by
        funext k; change s (v (x k)) + (x k - s (v (x k))) = x k
        abel
      change (fun k => s (v (x k)) + (splitUnit v s hs (x k)).val) ∈ U ↔ _ at h
      rwa [recon] at h
    exact ⟨b.frame.rectangleEquiv v s hs _ α hα ind U invariant _ localTest,fun _ => rfl⟩

end GeneralizedEuler.Section4
