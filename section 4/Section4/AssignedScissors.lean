module

public import Section4.LocalRVMeasure
import all Section4.LocalRVMeasure
import all Section4.Objects

/-! Zero, isomorphism, and cut relations for the invariant of a general
RV object, prior to proving the Cartesian product relation. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.LocalRVMeasure
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {P : Z .rv → Prop} {k : ℕ} {T : Type*} [AddCommMonoid T] (μ : LocalRVMeasure M S P k T)
  (existsWeight : ∀ U : RVObject M S k, ∃ t, μ.assigned U.carrier t)

def objectWeight (U : RVObject M S k) := (existsWeight U).choose

theorem objectWeight_iso (U V : RVObject M S k) (iso : U.Isomorphic M S V) :
    μ.objectWeight existsWeight U = μ.objectWeight existsWeight V :=
  μ.unique (existsWeight U).choose_spec (μ.transfer iso (existsWeight V).choose_spec)

theorem objectWeight_empty (U : RVObject M S k) (h : U.carrier = ∅) : μ.objectWeight existsWeight U = 0 := by
  exact μ.unique (existsWeight U).choose_spec ((congrArg (fun E => μ.assigned E 0) h).mpr μ.assigned_empty)

theorem assigned_cut {I : Type} (D A B : Set (I → Z .rv)) (h : Disjoint A B) (cover : A ∪ B = D)
    {x y : T} (hx : μ.assigned A x) (hy : μ.assigned B y) : μ.assigned D (x+y) := by
  let cells : Bool → Set (I → Z .rv) := fun b => cond b A B
  let weights : Bool → T := fun b => cond b x y
  have dj : Pairwise (fun i j => Disjoint (cells i) (cells j)) := by
    intro i j ne; cases i <;> cases j <;> first | exact (ne rfl).elim | exact h | exact h.symm
  have cov : (⋃ i, cells i) = D := by
    rw [← cover]; ext x
    refine Set.mem_iUnion.trans ⟨?_,?_⟩
    · rintro ⟨b,hb⟩; cases b with | false => exact Or.inr hb | true => exact Or.inl hb
    · rintro (ha | hb); exacts [⟨true,ha⟩,⟨false,hb⟩]
  have val (b) : μ.assigned (cells b) (weights b) := by cases b <;> first | exact hx | exact hy
  simpa [weights,Fintype.sum_bool,add_comm] using μ.assigned_partition cells weights dj cov val

theorem objectWeight_cut (U V W : RVObject M S k) (A B : Set (Fin U.arity → Z .rv))
    (h : Disjoint A B) (cover : A ∪ B = U.carrier)
    (left : RVDefinablyEquivalent M S.carrier A V.carrier) (right : RVDefinablyEquivalent M S.carrier B W.carrier) :
    μ.objectWeight existsWeight U = μ.objectWeight existsWeight V + μ.objectWeight existsWeight W :=
  μ.unique (existsWeight U).choose_spec (μ.assigned_cut _ _ _ h cover
    (μ.transfer left (existsWeight V).choose_spec) (μ.transfer right (existsWeight W).choose_spec))

end GeneralizedEuler.Section4.LocalRVMeasure
