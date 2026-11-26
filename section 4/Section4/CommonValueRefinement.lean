module

public import Section4.ValueScissors
public import Section4.LostCoordinates
import all Section4.ValueStratification

/-! Common fixed-base refinements of value partitions, with simultaneous
affine hull containment in the original coordinates. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {J : Language} [J.Structure V] {G : Submodule F V} {n : ℕ}
abbrev DefinablePiece (J : Language) [J.Structure V] (G : Submodule F V) (n : ℕ) :=
  IndependentPiece (fun _ D => (G : Set V).Definable J D) G n

theorem support_definable (h : ValueLanguage (J := J) G) (a : DefinablePiece J G n) :
    (G : Set V).Definable J a.support :=
  ValueObject.image_of_map a.frame.eval (h.frame a.frame) a.domain a.definable

/-- Intersect each pair of old supports before stratifying. Empty
intersections contribute no pieces. Both original partitions can then
be recovered by summing over the fibers of the two indexing maps. -/
theorem common_value_refinement {I K : Type} [Fintype I] [Fintype K]
    (h : ValueLanguage (J := J) G)
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set V).Definable J D))
    (a : I → DefinablePiece J G n) (b : K → DefinablePiece J G n)
    (ha : Pairwise (fun i j => Disjoint (a i).support (a j).support))
    (hb : Pairwise (fun i j => Disjoint (b i).support (b j).support)) :
    ∃ (l : ℕ) (c : Fin l → DefinablePiece J G n) (p : Fin l → I) (q : Fin l → K),
      (∀ i j, (a i).support ∩ (b j).support = ⋃ t : {t // p t = i ∧ q t = j}, (c t.val).support) ∧
      Pairwise (fun i j => Disjoint (c i).support (c j).support) ∧
      ∀ t, (c t).rank ≤ (a (p t)).rank ∧ (c t).rank ≤ (b (q t)).rank ∧
        ∀ z, ((a (p t)).frame.eval (((c t).frame.eval z) ∘ (a (p t)).frame.free) = (c t).frame.eval z) ∧
          ((b (q t)).frame.eval (((c t).frame.eval z) ∘ (b (q t)).frame.free) = (c t).frame.eval z) := by
  classical
  let intersection (ij : I × K) := (a ij.1).support ∩ (b ij.2).support
  have hd (ij) : (G : Set V).Definable J (intersection ij) :=
    (support_definable h _).inter (support_definable h _)
  choose count cell cover using fun ij => stratify_values _ (fun p D i => h.cut p D i) sat _ (hd ij)
  let Index := Σ ij, Fin (count ij)
  let e := (Fintype.equivFin Index).symm
  let c (t : Fin (Fintype.card Index)) := cell (e t).1 (e t).2
  let p (t : Fin (Fintype.card Index)) := (e t).1.1
  let q (t : Fin (Fintype.card Index)) := (e t).1.2
  have parent (t) {x} (hx : x ∈ (c t).support) : x ∈ intersection (e t).1 :=
    ((cover (e t).1 x).1).mpr ⟨(e t).2,hx⟩
  refine ⟨_,c,p,q,?_,?_,?_⟩
  · intro i j; ext x; rw [Set.mem_iUnion]; constructor
    · intro hx
      obtain ⟨k,hk⟩ := (cover (i,j) x).1.mp hx
      let t := e.symm ⟨(i,j),k⟩
      refine ⟨⟨t,by simp [p,q,t]⟩,?_⟩
      change x ∈ (cell (e (e.symm ⟨(i,j),k⟩)).1 (e (e.symm ⟨(i,j),k⟩)).2).support
      rw [Equiv.apply_symm_apply]; exact hk
    · rintro ⟨⟨t,hp,hq⟩,hx⟩
      exact ⟨hp ▸ (parent t hx).1,hq ▸ (parent t hx).2⟩
  · intro i j ne
    apply Set.disjoint_left.mpr
    intro x xi xj
    have pi : p i = p j := by
      by_contra neq
      exact Set.disjoint_left.mp (ha neq) (parent i xi).1 (parent j xj).1
    have qi : q i = q j := by
      by_contra neq
      exact Set.disjoint_left.mp (hb neq) (parent i xi).2 (parent j xj).2
    apply ne; apply e.injective
    obtain ⟨ij,u,ei⟩ : ∃ ij u, e i = ⟨ij,u⟩ := ⟨_,_,rfl⟩
    obtain ⟨kl,w,ej⟩ : ∃ kl w, e j = ⟨kl,w⟩ := ⟨_,_,rfl⟩
    have eq : (e i).1 = (e j).1 := Prod.ext pi qi
    rw [ei,ej] at eq ⊢
    change ij = kl at eq; subst kl
    change x ∈ (cell (e i).1 (e i).2).support at xi
    change x ∈ (cell (e j).1 (e j).2).support at xj
    rw [ei] at xi; rw [ej] at xj
    exact congrArg (Sigma.mk ij) ((cover ij x).2 _ _ xi xj)
  · intro t
    obtain ⟨α,hα,hi⟩ := (c t).independent
    have both := parent t (show (c t).frame.eval α ∈ (c t).support from ⟨α,hα,rfl⟩)
    have left := Set.image_subset_range _ _ both.1
    have right := Set.image_subset_range _ _ both.2
    exact ⟨(a (p t)).frame.refinement_rank _ α hi left,(b (q t)).frame.refinement_rank _ α hi right,
      fun z => ⟨(a (p t)).frame.refinement_hull _ α hi left z,(b (q t)).frame.refinement_hull _ α hi right z⟩⟩

end GeneralizedEuler.Section4
