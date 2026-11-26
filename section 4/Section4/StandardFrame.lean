module

public import Section4.SubframeCarrier
import all Section4.SubframeCarrier
public import Section4.ValueScissors
import all Section4.ValueFrames
import all Section4.PositiveRectangles
import all Section4.RelativeResidues
import all Section4.LostCoordinates
import all Section4.SliceComparison
import all Section4.ValueScissors

/-! Coordinates for a standard rectangle with m positive unit coordinates
followed by r free leading terms. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup T] [Module F T]
  (G : Submodule F V) (m r : ℕ)
def stdLeft : Fin m ↪ Fin (m+r) := Function.Embedding.inl.trans finSumFinEquiv.toEmbedding
def stdRight : Fin r ↪ Fin (m+r) := Function.Embedding.inr.trans finSumFinEquiv.toEmbedding

def standardFrame : ValueFrame G r (m+r) where
  free := stdRight m r
  rows := unitColumns (stdRight m r)
  shift := 0
  freeRow i j := by simp [unitColumns,(stdRight m r).injective.eq_iff,eq_comm]
  freeShift _ := rfl

theorem left_outside (i : Fin m) : stdLeft m r i ∉ Set.range (stdRight m r) := by
  rintro ⟨j,eq⟩
  have bad : (Sum.inr j : Fin m ⊕ Fin r) = Sum.inl i := finSumFinEquiv.injective eq
  cases bad

def standardIndex : Fin m ≃ (standardFrame G m r).dependent := by
  let e (i : Fin m) : (standardFrame G m r).dependent := ⟨stdLeft m r i,left_outside m r i⟩
  refine Equiv.ofBijective e ⟨fun _ _ h => (stdLeft m r).injective (congrArg Subtype.val h),?_⟩
  rintro ⟨j,hj⟩
  obtain ⟨s,rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin r ≃ Fin (m+r)).surjective j
  cases s with
  | inl i => exact ⟨i,rfl⟩
  | inr i => exact (hj ⟨i,rfl⟩).elim

variable (v : T →ₗ[F] V) (s : V →ₗ[F] T)
theorem standard_assemble_left (z : Fin r → T) (b : (standardFrame G m r).dependent → v.ker) (i : Fin m) :
    (standardFrame G m r).assemble v s z b (stdLeft m r i) = (b (standardIndex G m r i)).val := by
  let A := standardFrame G m r
  have zero (j : Fin r) : A.rows (stdLeft m r i) j = 0 :=
    ite_eq_right (fun eq => left_outside m r i ⟨j,eq⟩)
  change (∑ j, A.rows (stdLeft m r i) j • z j) + s 0 + (A.extendResidues v b ((standardIndex G m r i).val)).val = _
  rw [A.extend_dependent]; simp [zero]

theorem standard_assemble_right (z : Fin r → T) (b : (standardFrame G m r).dependent → v.ker) :
    (standardFrame G m r).assemble v s z b ∘ stdRight m r = z :=
  (standardFrame G m r).assemble_free v s z b

variable {m r}
theorem standard_carrier (D : Set (Fin r → V)) (B : Set (Fin m → v.ker)) :
    (standardFrame G m r).assemblySet s D {b | b ∘ standardIndex G m r ∈ B} =
      cartesian ((fun b : Fin m → v.ker => v.ker.subtype ∘ b) '' B) {z | v ∘ z ∈ D} := by
  let A := standardFrame G m r
  let idx := standardIndex G m r
  ext x; constructor
  · rintro ⟨⟨z,b⟩,⟨hz,hb⟩,rfl⟩
    exact ⟨⟨b ∘ idx,hb,funext fun i => (standard_assemble_left G m r v s z b i).symm⟩,
      (congrArg (fun w => v ∘ w ∈ D) (standard_assemble_right G m r v s z b)).mpr hz⟩
  · rintro ⟨⟨t,ht,eq⟩,hz⟩
    let b := t ∘ idx.symm
    let z := x ∘ stdRight m r
    have hb : b ∘ idx ∈ B := by
      have eq : b ∘ idx = t := funext fun i => congrArg t (idx.symm_apply_apply i)
      rwa [eq]
    refine ⟨(z,b),⟨hz,hb⟩,?_⟩
    funext j
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin r ≃ Fin (m+r)).surjective j
    cases i with
    | inl i =>
      change A.assemble v s z b (stdLeft m r i) = _
      rw [standard_assemble_left]
      exact (congrArg (fun q => (t q).val) (idx.symm_apply_apply i)).trans (congrFun eq i)
    | inr i => exact congrFun (standard_assemble_right G m r v s z b) i

end GeneralizedEuler.Section4
