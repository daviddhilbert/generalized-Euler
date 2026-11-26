module

public import Section4.AssignedScissors
public import Section4.ResidueScissors
import all Section4.ResidueScissors
import all Section4.LocalRVMeasure
import all Section4.FiniteScissors
import all Section4.Objects

/-! A partition by residue objects computes the same sum in RES and in
the fixed-base valuation. The identifications may use different tuple arities. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {Γ : Type*} {v : Z .rv → Γ} {P : Z .rv → Prop} {T : Type*} [CommSemiring T] {k : ℕ}
  (μ : LocalRVMeasure M S P k T) (w : ResidueSemiring M S v →+* T)

theorem assigned_residue_partition (U : RVObject M S k) (hu : U.IsResidue M S v) {I : Type} [Fintype I]
    (D : I → Set (Fin U.arity → Z .rv)) (hd : ∀ i, isRVSet M S (D i))
    (disj : Pairwise (fun i j => Disjoint (D i) (D j))) (cv : (⋃ i, D i) = U.carrier)
    (B : I → RVObject M S k) (hb : ∀ i, (B i).IsResidue M S v)
    (iso : ∀ i, RVDefinablyEquivalent M S.carrier (D i) (B i).carrier)
    (hw : ∀ i, μ.assigned (B i).carrier (w (residueClass (B i) (hb i)))) :
    μ.assigned U.carrier (w (residueClass U hu)) := by
  have partition := residue_class_partition U hu D hd disj cv
  have eq : residueClass U hu = ∑ i, residueClass (B i) (hb i) :=
    partition.trans (Finset.sum_congr rfl fun i _ => residue_class_iso _ _ _ _ (iso i))
  rw [eq,map_sum]
  exact μ.assigned_partition _ _ disj cv (fun i => μ.transfer (iso i) (hw i))

end GeneralizedEuler.Section4
