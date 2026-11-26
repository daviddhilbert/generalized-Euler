module

public import Section4.AxialFiberCharts
import all Section4.AxialFiberCharts
import all Section4.ValueConePartition
import all Section4.AdaptedParameterCones
import all Section4.SpecializedConePartitions
import all Section4.LinearSignTransfer
import all Section4.ConeFiberPresentations

/-! Every finite Boolean combination of affine inequalities over the old
value subgroup has a box presentation in its original degree. Homogenizing
the constant terms makes the old parameter tuple explicit. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set FirstOrder PaddedBox ValueObject
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {G : Submodule F V} {k m : ℕ}

def signs {I : Type} (a : I → PairSpace (Fin k) (Fin m) F →ₗ[F] F) (x : PairSpace (Fin k) (Fin m) V) (i : I) :=
  decide (0 ≤ evalRow ((a i).comp packLinear.symm.toLinearMap) (pack x.1 x.2))

def SemilinearOver (G : Submodule F V) (D : Set (Fin k → V)) : Prop :=
  ∃ (m : ℕ) (p : Fin m → G) (n : ℕ) (a : Fin n → PairSpace (Fin k) (Fin m) F →ₗ[F] F)
    (accept : (Fin n → Bool) → Prop), ∀ x, x∈D ↔ accept (signs a (x,fun j => (p j : V)))

omit [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F V] in
theorem valueMixed_oriented {I : Type} (a : I → PairSpace (Fin k) (Fin m) F →ₗ[F] F) (b : I → Bool)
    (x : PairSpace (Fin k) (Fin m) V) :
    valueMixed (oriented a b) (fun i => b i=false) x ↔ signs a x=b := by
  classical
  have rowneg (i) : evalRow ((-a i).comp packLinear.symm.toLinearMap) (pack x.1 x.2) =
      -evalRow ((a i).comp packLinear.symm.toLinearMap) (pack x.1 x.2) := by
    simp [evalRow,linearTest,neg_smul,Finset.sum_neg_distrib]
  rw [funext_iff]
  apply forall_congr'
  intro i
  dsimp only
  cases h : b i with
  | false =>
    have neg : oriented a b i = -a i := by simp [oriented,h]
    rw [neg,rowneg]
    simp [signs]
    exact fun h => h.le
  | true => simp [oriented,signs,h]

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem triangulate_union {I : Type} [Fintype I] (D : I → Set (Fin k → V))
    (dj : Pairwise (fun i j => Disjoint (D i) (D j))) (tri : ∀ i, HasFiberTriangulation (G := G) (D i)) :
    HasFiberTriangulation (G := G) (⋃ i, D i) := by
  classical
  choose n c disj cov using tri
  let T := (i : I) × Fin (n i)
  let e := (Fintype.equivFin T).symm
  have subset (i j) : (c i j).carrier ⊆ D i := cov i ▸ subset_iUnion (fun j => (c i j).carrier) j
  refine ⟨_,fun t => c (e t).1 (e t).2,fun i j ne => ?_,?_⟩
  · dsimp only
    rcases eq_or_ne (e i).1 (e j).1 with same|diff
    · generalize hi : e i = a at same ⊢
      generalize hj : e j = b at same ⊢
      rcases a with ⟨u,v⟩; rcases b with ⟨w,z⟩
      dsimp only at same ⊢
      subst w
      exact disj u (fun eq => ne (e.injective (hi.trans ((congrArg (Sigma.mk u) eq).trans hj.symm))))
    · exact (dj diff).mono (subset _ _) (subset _ _)
  · ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨t,ht⟩; exact ⟨_,subset _ _ ht⟩
    · rintro ⟨i,hi⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp ((cov i).symm ▸ hi)
      exact ⟨e.symm ⟨i,j⟩,by rw [e.apply_symm_apply]; exact hj⟩

theorem triangulate_semilinear {D : Set (Fin k → V)} (hD : SemilinearOver G D) : HasFiberTriangulation (G := G) D := by
  classical
  obtain ⟨m,p,n,a,accept,law⟩ := hD
  let X := PairSpace (Fin k) (Fin m) F
  let J := Fin n ⊕ (Fin k ⊕ Fin m)
  let tests : J → X →ₗ[F] F := Sum.elim a (fun i => (LinearMap.proj i).comp packLinear.toLinearMap)
  let T := {b : J → Bool // accept (fun i => b (.inl i))}
  let cell (b : T) := {x : Fin k → V | signs tests (x,fun j => (p j : V))=b.val}
  have tri (b : T) : HasFiberTriangulation (G := G) (cell b) := by
    have pointed (w : X) (h : ∀ i, oriented tests b.val i w=0) : w=0 := by
      apply packLinear.injective
      funext j
      have eq := h (.inr j)
      cases hj : b.val (.inr j) <;> simpa [oriented,hj,tests,LinearMap.comp_apply] using eq
    have cv := triangulate_mixed (oriented tests b.val) pointed (fun i => b.val i=false) p
    have eq : {x | valueMixed (oriented tests b.val) (fun i => b.val i=false) (x,fun j => (p j : V))} = cell b :=
      Set.ext (fun x => valueMixed_oriented tests b.val (x,fun j => (p j : V)))
    exact eq ▸ cv
  have disj : Pairwise (fun i j => Disjoint (cell i) (cell j)) := fun _ _ ne =>
    Set.disjoint_left.mpr (fun {x} hx hy => ne (Subtype.ext (Eq.trans (Eq.symm hx) hy)))
  have eq : (⋃ b, cell b)=D := by
    ext x
    rw [mem_iUnion,law]
    constructor
    · rintro ⟨b,hb⟩
      have h : (fun i => b.val (.inl i))=signs a (x,fun j => (p j : V)) := funext fun i => (congrFun hb (.inl i)).symm
      exact h ▸ b.property
    · intro h; exact ⟨⟨signs tests (x,fun j => (p j : V)),h⟩,rfl⟩
  exact eq ▸ triangulate_union cell disj tri

variable {J : Language} [J.Structure V] (L : BoxLanguage (J := J) G)
  (order : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})

include order in
theorem semilinear_box_presentation (D : Set (Fin k → V)) (hd : (G : Set V).Definable J D)
    (hD : SemilinearOver G D) : ∃ p : Presentation G k, presentationValue L p = pieceClass D hd :=
  box_presentation_of_triangulation L order D hd (triangulate_semilinear hD)

end GeneralizedEuler.Section4.Polyhedral
