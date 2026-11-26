module

public import Section5.GradedRVProducts
public import Section5.GradedScissorRealization
import all Section4.PositivePresentations

/-! Every positive class is represented by finitely many actual graded
RV objects. This allows class equality to be used with tag partitions. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  (M : SortedStructure L E X) (S : SortedSubstructure M)

def degreeZeroUnit : RVObject M S 0 :=
  identityRVObject Set.univ
    ⟨.imp .falsum .falsum,fun _ => ⟨fun _ h => h,fun _ => Set.mem_univ _⟩⟩
    (fun _ _ i => i.elim0)

theorem degreeZeroUnit_class : objectClass M S ⟨0,degreeZeroUnit M S⟩ = 1 := by
  unfold objectClass
  rw [← map_one (ringConGen (RVRelation M S)).mk']
  apply scissors_sound M S
  apply RVRelation.one
  refine ⟨Fin.elim0,?_⟩
  change (Set.univ : Set (Fin 0 → X .rv)) = {Fin.elim0}
  exact (Set.eq_univ_of_forall (fun x => Set.mem_singleton_iff.2 (Subsingleton.elim x _))).symm

/-- Every element of the positive scissor semiring is a finite sum of
classes of fixed-base graded RV objects. -/
theorem positive_class_represented (a : RVSemiring M S) :
    ∃ (n : ℕ) (U : Fin n → GradedObject M S), a = ∑ i, objectClass M S (U i) := by
  classical
  let cls := objectClass M S
  let mul (u v : GradedObject M S) : GradedObject M S :=
    ⟨u.1+v.1,RVObject.cartesianProduct u.2 v.2⟩
  let q := (ringConGen (RVRelation M S)).mk'
  obtain ⟨p,rfl⟩ := (ringConGen (RVRelation M S)).mk'_surjective a
  change ∃ (n : ℕ) (U : Fin n → GradedObject M S), q p = ∑ i, cls (U i)
  induction p using MvPolynomial.induction_on with
  | C n =>
    refine ⟨n,fun _ => ⟨0,degreeZeroUnit M S⟩,?_⟩
    rw [show MvPolynomial.C n = (n : RVExpression M S) from map_natCast _ n,map_natCast]
    simp only [cls,degreeZeroUnit_class,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_one]
  | add p r hp hr =>
    obtain ⟨n,U,hU⟩ := hp
    obtain ⟨m,V,hV⟩ := hr
    let W : Fin (n+m) → GradedObject M S := Sum.elim U V ∘ finSumFinEquiv.symm
    refine ⟨n+m,W,?_⟩
    rw [map_add,hU,hV,← Fintype.sum_equiv finSumFinEquiv (fun i => cls (Sum.elim U V i))
      (fun i => cls (W i)) (by intro i; simp [W])]
    exact (Fintype.sum_sum_type (fun i : Fin n ⊕ Fin m => cls (Sum.elim U V i))).symm
  | mul_X p u h =>
    obtain ⟨n,U,hU⟩ := h
    refine ⟨n,fun i => mul (U i) u,?_⟩
    rw [map_mul,hU,Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (RVObject.cartesianProduct_class (U i).2 u.2).symm

end GeneralizedEuler.Section5
