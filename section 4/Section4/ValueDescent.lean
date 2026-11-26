module

public import Section4.ValueTagComparison
import all Section4.Factors
import all Section4.ValueScissors
import all Section4.ValueTagComparison

/-! Descent from single value pieces to the presented graded semiring, including
the cut and product relations with arbitrary target tags. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder MvPolynomial
variable {V : Type*} {J : Language} [J.Structure V] {A : Set V}
  {T : Type*} [CommSemiring T]

structure PieceMeasure (J : Language) {V : Type*} [J.Structure V] (A : Set V)
    (T : Type*) [CommSemiring T] where
  weight : ∀ {k}, ValueWeight J A k T
  empty : ∀ k, weight (∅ : Set (Fin k → V)) Set.definable_empty = 0
  one : weight (Set.univ : Set (Fin 0 → V)) Set.definable_univ = 1
  cut : ∀ {k} (D E : Set (Fin k → V)) (hd : A.Definable J D) (he : A.Definable J E),
    Disjoint D E → weight (D ∪ E) (hd.union he) = weight D hd + weight E he
  iso : ∀ {k} (D E : Set (Fin k → V)) (hd : A.Definable J D) (he : A.Definable J E) (e : D ≃ E),
    A.Definable J {w : Fin k ⊕ Fin k → V | ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      weight D hd = weight E he
  prod : ∀ {k l} (D : Set (Fin k → V)) (E : Set (Fin l → V))
    (hd : A.Definable J D) (he : A.Definable J E),
    weight (cartesian D E) (cartesian_definable hd he) = weight D hd * weight E he

namespace PieceMeasure
variable (μ : PieceMeasure J A T)
def tagged (U : Graded (J := J) A) := ∑ i, μ.weight (U.2.piece i) (U.2.isDefinable i)

theorem partition {I : Type} [Fintype I] {k} (D : Set (Fin k → V)) (hd : A.Definable J D)
    (d : I → Set (Fin k → V)) (hs : ∀ i, A.Definable J (d i))
    (disj : Pairwise (fun i j => Disjoint (d i) (d j))) (cover : ⋃ i, d i = D) :
    μ.weight D hd = ∑ i, μ.weight _ (hs i) := by
  subst D
  exact (finite_scissor_sum μ.weight Set.definable_empty (μ.empty k) (fun x y => x.union y) μ.cut d hs disj).choose_spec

theorem sum_iso {I H : Type} [Fintype I] [Fintype H] {k : ℕ}
    (D : I → Set (Fin k → V)) (E : H → Set (Fin k → V)) (hd : ∀ i, A.Definable J (D i))
    (he : ∀ j, A.Definable J (E j)) (e : (Σ i, D i) ≃ (Σ j, E j))
    (hg : ∀ i j, A.Definable J (sliceGraph D E e i j)) :
    ∑ i, μ.weight _ (hd i) = ∑ j, μ.weight _ (he j) :=
  compare_tags μ.weight (fun D h d hs => μ.partition D h d hs) μ.iso D E hd he e hg

private def joinTags {I H : Type} {k} (D : I → Set (Fin k → V)) (E : H → Set (Fin k → V)) :
    ((Σ i, D i) ⊕ (Σ j, E j)) ≃ (Σ t : I ⊕ H, ↥(Sum.elim D E t)) where
  toFun
    | .inl ⟨i,x⟩ => ⟨.inl i,x⟩
    | .inr ⟨j,y⟩ => ⟨.inr j,y⟩
  invFun
    | ⟨.inl i,x⟩ => .inl ⟨i,x⟩
    | ⟨.inr j,y⟩ => .inr ⟨j,y⟩
  left_inv x := by cases x <;> rfl
  right_inv := fun ⟨i,x⟩ => by cases i <;> rfl

theorem sum_cut {k} (U B C : Over (J := J) A k) (h : U.IsCut A B C) :
    μ.tagged ⟨k,U⟩ = μ.tagged ⟨k,B⟩ + μ.tagged ⟨k,C⟩ := by
  classical
  obtain ⟨e,hB,hC⟩ := h
  let join := joinTags B.piece C.piece
  let f := e.trans join
  let D := Sum.elim B.piece C.piece
  have hd (j) : A.Definable J (D j) := by cases j with | inl j => exact B.isDefinable j | inr j => exact C.isDefinable j
  have hg (i j) : A.Definable J (sliceGraph U.piece D f i j) := by
    cases j with
    | inl j =>
      convert hB i j using 1
      ext w; unfold sliceGraph
      simp only [Set.mem_ofPred_eq]
      refine exists_congr fun x => and_congr_right fun _ => exists_congr fun y => and_congr_right fun _ => ?_
      exact join.eq_symm_apply.symm
    | inr j =>
      convert hC i j using 1
      ext w; unfold sliceGraph
      simp only [Set.mem_ofPred_eq]
      refine exists_congr fun x => and_congr_right fun _ => exists_congr fun y => and_congr_right fun _ => ?_
      exact join.eq_symm_apply.symm
  exact (μ.sum_iso _ _ _ hd f hg).trans (Fintype.sum_sum_type _)

private def pairTags {I H : Type} {k l} (D : I → Set (Fin k → V)) (E : H → Set (Fin l → V)) :
    ((Σ i, D i) × (Σ j, E j)) ≃ Σ t : I × H, cartesian (D t.1) (E t.2) where
  toFun := fun ⟨⟨i,x⟩,⟨j,y⟩⟩ => ⟨(i,j),cartesianEquiv _ _ (x,y)⟩
  invFun := fun ⟨⟨i,j⟩,z⟩ => (⟨i,((cartesianEquiv _ _).symm z).1⟩,⟨j,((cartesianEquiv _ _).symm z).2⟩)
  left_inv := fun ⟨⟨i,x⟩,⟨j,y⟩⟩ => by simp
  right_inv := fun ⟨⟨i,j⟩,z⟩ => by simp

theorem sum_product {k l} (U : Over (J := J) A k) (B : Over (J := J) A l)
    (W : Over (J := J) A (k+l)) (h : U.IsProduct A B W) :
    μ.tagged ⟨k+l,W⟩ = μ.tagged ⟨k,U⟩ * μ.tagged ⟨l,B⟩ := by
  classical
  obtain ⟨e,hg⟩ := h
  let pair := pairTags U.piece B.piece
  let f := pair.symm.trans e
  let D (t : Fin U.tags × Fin B.tags) := cartesian (U.piece t.1) (B.piece t.2)
  have hd (t) : A.Definable J (D t) := cartesian_definable (U.isDefinable _) (B.isDefinable _)
  have graph (t : Fin U.tags × Fin B.tags) (j) : A.Definable J (sliceGraph D W.piece f t j) := by
    rcases t with ⟨a,b⟩
    let rename := Sum.map (finSumFinEquiv (m := k) (n := l)) (id (α := Fin (k+l)))
    convert (hg a b j).preimage_comp rename using 1
    ext w
    constructor
    · rintro ⟨x,hx,z,hz,eq⟩
      let p := (cartesianEquiv _ _).symm x
      exact ⟨p.1,p.2,by exact congrArg (· ∘ finSumFinEquiv ∘ Sum.inl) hx,
        by exact congrArg (· ∘ finSumFinEquiv ∘ Sum.inr) hx,z,hz,eq⟩
    · rintro ⟨x,y,hx,hy,z,hz,eq⟩
      let q := cartesianEquiv _ _ (x,y)
      refine ⟨q,?_,z,hz,?_⟩
      · funext i; obtain ⟨p,rfl⟩ := finSumFinEquiv.surjective i
        cases p with
        | inl i => simpa [q,cartesianEquiv,rename] using congrFun hx i
        | inr j => simpa [q,cartesianEquiv,rename] using congrFun hy j
      · change e (pair.symm (pair (⟨a,x⟩,⟨b,y⟩))) = _
        rwa [pair.symm_apply_apply]
  have eq := (μ.sum_iso D W.piece hd W.isDefinable f graph).symm
  refine eq.trans ?_
  rw [Fintype.sum_prod_type, tagged, tagged, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => μ.prod _ _ _ _

theorem sum_empty {k} (U : Over (J := J) A k) (h : IsEmpty (U.points A)) :
    μ.tagged ⟨k,U⟩ = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have eq : U.piece i = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => h.false ⟨i,x,hx⟩
  convert μ.empty k using 2

theorem sum_one (U : Over (J := J) A 0) (h : Nonempty (Unique (U.points A))) :
    μ.tagged ⟨0,U⟩ = 1 := by
  classical
  let u := h.some.default
  have all_eq (x : U.points A) : x = u := h.some.uniq x
  change (∑ i, μ.weight (U.piece i) (U.isDefinable i)) = _
  rw [Finset.sum_eq_single u.1]
  · have eq : U.piece u.1 = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun y => (Subsingleton.elim u.2.val y) ▸ u.2.property
    convert μ.one using 2
  · intro i _ ne
    have eq : U.piece i = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
      ne (congrArg Sigma.fst (all_eq ⟨i,x,hx⟩))
    convert μ.empty 0 using 2
  · simp

def descend : SemiringOfSets (J := J) A →+* T := by
  let f := MvPolynomial.eval₂Hom (Nat.castRingHom T) μ.tagged
  apply (ringConGen (Relation (J := J) A)).lift f
  apply RingCon.ringConGen_le.mpr
  intro a b rel
  cases rel with
  | iso U W h =>
    obtain ⟨e,he⟩ := h
    simpa [f,tagged] using μ.sum_iso U.piece W.piece U.isDefinable W.isDefinable e he
  | empty U h => simpa [f] using μ.sum_empty U h
  | one U h => simpa [f] using μ.sum_one U h
  | cut U B C h => simpa [f] using μ.sum_cut U B C h
  | prod U B W h => simpa [f] using μ.sum_product U B W h

@[simp] theorem descend_piece {k} (D : Set (Fin k → V)) (hd : A.Definable J D) :
    μ.descend (pieceClass D hd) = μ.weight D hd := by
  change MvPolynomial.eval₂ (Nat.castRingHom T) μ.tagged (X ⟨k,single D hd⟩) = _
  rw [MvPolynomial.eval₂_X]
  simp [tagged,single]

end PieceMeasure
end GeneralizedEuler.Section4.ValueObject
