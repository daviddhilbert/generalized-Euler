module

public import Section4.BaseAndDimension
public import Section4.FiniteScissors
import all Section4.Objects
import all Section4.FiniteScissors

/-! Remark 4.1 chooses representatives for *all* values of a finite-image
RV object over the original base. Remove each value fiber already met by a
base tuple, then apply the fixed-base witness property to the remainder. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z}
  {S : SortedSubstructure M} {I : Type} {V : Type*} (v : (I → Z .rv) → V)
  (witness : ∀ D : Set (I → Z .rv), isRVSet M S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
  (fiber : ∀ x : I → Z .rv, (∀ i, x i ∈ S.carrier .rv) → isRVSet M S {y | v y = v x})

include witness fiber in
theorem finite_base_fibers (U : Set (I → Z .rv)) (du : isRVSet M S U) (fin : (v '' U).Finite) :
    ∀ a ∈ v '' U, ∃ x ∈ U, (∀ i, x i ∈ S.carrier .rv) ∧ v x = a := by
  classical
  let seen := {a | ∃ x ∈ U, (∀ i, x i ∈ S.carrier .rv) ∧ v x = a}
  have sub : seen ⊆ v '' U := fun _ ⟨x,hx,_,eq⟩ => ⟨x,hx,eq⟩
  let sf := fin.subset sub
  let : Fintype seen := sf.fintype
  have each (a : seen) : isRVSet M S {y | v y = a.val} := by
    obtain ⟨x,_,hx,eq⟩ := a.property
    rw [← eq]; exact fiber x hx
  let idx := (Fintype.equivFin seen).symm
  let old := ⋃ i, {y | v y = (idx i).val}
  have old_def : isRVSet M S old := isRVSet_iUnion (fun i => each (idx i))
  intro a ha
  by_contra h
  obtain ⟨x,hx,eq⟩ := ha
  have newPoint : x ∈ U ∩ oldᶜ := ⟨hx,fun m => by
    obtain ⟨b,hb⟩ := Set.mem_iUnion.mp m
    exact h ((show a = (idx b).val from eq.symm.trans hb).symm ▸ (idx b).property)⟩
  obtain ⟨y,hy,hyS⟩ := witness (U ∩ oldᶜ) (du.inter old_def.compl) ⟨x,newPoint⟩
  let b : seen := ⟨v y,y,hy.1,hyS,rfl⟩
  exact hy.2 (Set.mem_iUnion.mpr ⟨idx.symm b,by simp [b]⟩)

end GeneralizedEuler.Section4
