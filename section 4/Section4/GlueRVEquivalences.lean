module

public import Section4.FiniteScissors
public import Mathlib.Data.Set.Lattice.Disjoint
import all Section2.RVDefinableEquivalence

/-! Gluing fixed-base RV bijections while retaining their action on each piece. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {L : Language} {F : Type*} {Z : TCsort → Type*}
  {M : SortedStructure L F Z} {S : SortedSubstructure M}
  {I J H : Type} [Finite H] {D : Set (I → Z .rv)} {C : Set (J → Z .rv)}

theorem glue_rv_equivalences (U : H → Set (I → Z .rv)) (W : H → Set (J → Z .rv))
    (src : (⋃ i, U i) = D) (dst : (⋃ i, W i) = C)
    (ds : Pairwise fun i j => Disjoint (U i) (U j))
    (dt : Pairwise fun i j => Disjoint (W i) (W j))
    (f : ∀ i, U i ≃ W i)
    (hf : ∀ i, SortedDefinableOver M S.carrier (rvGraph fun x => (f i x).val)) :
    ∃ e : D ≃ C, SortedDefinableOver M S.carrier (rvGraph fun x => (e x).val) ∧
      ∀ i (x : U i) (y : D), x.val = y.val → (e y).val = (f i x).val := by
  subst D; subst C
  let srcTag := Set.unionEqSigmaOfDisjoint ds
  let dstTag := Set.unionEqSigmaOfDisjoint dt
  let e := srcTag.trans ((Equiv.sigmaCongrRight f).trans dstTag.symm)
  have law (i : H) (x : U i) (y : ⋃ i, U i) (h : x.val = y.val) : (e y).val = (f i x).val := by
    have eq : srcTag.symm ⟨i,x⟩ = y := Subtype.ext h
    rw [← eq]; change (dstTag.symm ((Equiv.sigmaCongrRight f) (srcTag (srcTag.symm _)))).val = _
    rw [Equiv.apply_symm_apply]; rfl
  refine ⟨e,?_,law⟩
  convert SortedDefinableOver.iUnion hf using 1
  ext w
  change (∃ y : ⋃ i, U i, y.val = w .rv ∘ Sum.inl ∧ (e y).val = w .rv ∘ Sum.inr) ↔
    w ∈ ⋃ i, rvGraph (fun x => (f i x).val)
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨y,hy,he⟩
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp y.property
    exact ⟨i,⟨y.val,hi⟩,hy,(law i ⟨y.val,hi⟩ y rfl).symm.trans he⟩
  · rintro ⟨i,x,hx,he⟩
    let y : ⋃ i, U i := ⟨x.val,Set.mem_iUnion.mpr ⟨i,x.property⟩⟩
    exact ⟨y,hx,(law i x y rfl).trans he⟩

end GeneralizedEuler.Section4
