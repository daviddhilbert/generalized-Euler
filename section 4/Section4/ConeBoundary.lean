module

public import Section4.ProjectedConeRays
import all Section4.ProjectedConeRays

/-! Moving through a face until a new inequality becomes tight. The
finite ratio minimum works over every ordered field of exponents. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {I : Type*} [Fintype I]

theorem first_boundary (x w : I → F) (hx : ∀ i, 0 ≤ x i)
    (active : ∀ i, x i=0 → 0≤w i) (toward : ∃ i, w i<0) :
    ∃ t : F, 0<t ∧ (∀ i, 0≤x i + t*w i) ∧ ∃ i, 0<x i ∧ x i+t*w i=0 := by
  classical
  let falling := Finset.univ.filter (fun i => w i < 0)
  let time (i : I) := x i / (-w i)
  have nonempty : falling.Nonempty := by
    obtain ⟨i,h⟩ := toward
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  obtain ⟨j,hj,minimal⟩ := falling.exists_min_image time nonempty
  have neg : w j < 0 := (Finset.mem_filter.mp hj).2
  have pos : 0 < x j := lt_of_le_of_ne (hx _) (fun h => neg.not_ge (active _ h.symm))
  have tpos : 0 < time j := div_pos pos (neg_pos.mpr neg)
  refine ⟨time j,tpos,fun i => ?_,j,pos,?_⟩
  · by_cases hi : w i < 0
    · have bound := minimal i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
      have h := (le_div_iff₀ (neg_pos.mpr hi)).mp bound
      linarith
    · exact add_nonneg (hx _) (mul_nonneg tpos.le (le_of_not_gt hi))
  · have h : time j * (-w j) = x j := div_mul_cancel₀ _ (neg_ne_zero.mpr neg.ne)
    linarith

def live (x : I → F) : Finset I := Finset.univ.filter (fun i => 0 < x i)

omit [IsStrictOrderedRing F] in
theorem live_card_drop (x y : I → F) (hx : ∀ i, 0 ≤ x i)
    (tight : ∀ i, x i = 0 → y i = 0) (lost : ∃ i, 0 < x i ∧ y i = 0) :
    (live y).card < (live x).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · intro i hi
    have pos := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_le_of_ne (hx _) (fun e => pos.ne' (tight _ e.symm))⟩
  · rintro h
    obtain ⟨i,pos,eq⟩ := lost
    have mem : i ∈ live x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,pos⟩
    exact (Finset.mem_filter.mp (h.symm ▸ mem : i ∈ live y)).2.ne' eq

variable {E : Type*} [AddCommGroup E] [Module F E] (a : I → E →ₗ[F] F)

def testMap (x : E) (i : I) := a i x
def totalTest (x : E) := ∑ i, a i x

/-- A normalized point is a vertex exactly when its tight inequalities
and the normalization cut out a single point in its affine hull. -/
def IsVertex (x : E) : Prop :=
  x ∈ polyCone a ∧ totalTest a x = 1 ∧
    ∀ w : E, (∀ i, a i x=0 → a i w=0) → totalTest a w=0 → w=0

include a in
theorem vertex_extreme (x : E) (h : IsVertex a x) :
    IsExtreme F (polyCone a) (positiveRay (F := F) x) := by
  refine ⟨?_,?_⟩
  · rintro _ ⟨t,ht,rfl⟩ i; simpa using mul_nonneg ht (h.1 i)
  · rintro u hu v hv z ⟨t,ht,rfl⟩ ⟨p,q,hp,hq,pq,eq⟩
    have tight (i) (hi : a i x=0) : a i u=0 := by
      have e := congrArg (a i) eq
      simp only [map_add,map_smul,smul_eq_mul,hi,mul_zero] at e
      have := mul_nonneg hq.le (hv i)
      exact (mul_eq_zero.mp (le_antisymm (by linarith) (mul_nonneg hp.le (hu i)))).resolve_left hp.ne'
    let s := totalTest a u
    have eq0 : u-s • x=0 := h.2.2 _ (fun i hi => by simp [hi,tight i hi]) (by
      simp only [totalTest,map_sub,Finset.sum_sub_distrib,map_smul,smul_eq_mul,← Finset.mul_sum]
      change s-s*totalTest a x=0
      rw [h.2.1,mul_one,sub_self])
    exact ⟨s,Finset.sum_nonneg fun i _ => hu i,(sub_eq_zero.mp eq0).symm⟩

omit [IsStrictOrderedRing F] in
theorem vertex_unique {x y : E} (hx : IsVertex a x) (hy : IsVertex a y)
    (equal : live (testMap a x) = live (testMap a y)) : x=y := by
  apply sub_eq_zero.mp
  apply hx.2.2
  · intro i eq
    have e : a i y=0 := by
      apply le_antisymm _ (hy.1 _)
      by_contra! h
      have mem : i ∈ live (testMap a y) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
      exact ((Finset.mem_filter.mp (equal.symm ▸ mem : i ∈ live (testMap a x))).2).ne' eq
    simp [eq,e]
  · change (∑ i, a i (x-y))=0
    simp only [map_sub,Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hx.2.1.trans hy.2.1.symm)

end GeneralizedEuler.Section4.Polyhedral
