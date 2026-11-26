module

public import Section4.IntervalScales

/-! Finite homogeneous linear sign tests on an ordered vector space
over F have the same possible patterns as over F, in the direction needed
to transfer a polyhedral partition from F to the value group. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set

private theorem between_finsets {W : Type*} [LinearOrder W] [DenselyOrdered W] [NoMinOrder W] [NoMaxOrder W] [Nonempty W]
    (a b : Finset W) (sep : ∀ x ∈ a, ∀ y ∈ b, x < y) :
    ∃ t, (∀ x ∈ a, x<t) ∧ ∀ y ∈ b, t<y := by
  classical
  by_cases ha : a.Nonempty
  · by_cases hb : b.Nonempty
    · obtain ⟨t,l,r⟩ := exists_between (sep _ (a.max'_mem ha) _ (b.min'_mem hb))
      exact ⟨t,fun x h => (a.le_max' x h).trans_lt l,fun y h => r.trans_le (b.min'_le y h)⟩
    · obtain ⟨t,l⟩ := exists_gt (a.max' ha)
      exact ⟨t,fun x h => (a.le_max' x h).trans_lt l,fun y h => (hb ⟨y,h⟩).elim⟩
  · by_cases hb : b.Nonempty
    · obtain ⟨t,r⟩ := exists_lt (b.min' hb)
      exact ⟨t,fun x h => (ha ⟨x,h⟩).elim,fun y h => r.trans_le (b.min'_le y h)⟩
    · exact ⟨Classical.arbitrary W,fun x h => (ha ⟨x,h⟩).elim,fun y h => (hb ⟨y,h⟩).elim⟩

private theorem transfer_cut {I V W : Type*} [Fintype I] [LinearOrder V] [LinearOrder W] [DenselyOrdered W]
    [NoMinOrder W] [NoMaxOrder W] [Nonempty W] (p : I → V) (q : I → W)
    (order : ∀ i j, p i ≤ p j ↔ q i ≤ q j) (x : V) :
    ∃ t, ∀ i, (p i ≤ x ↔ q i ≤ t) ∧ (x ≤ p i ↔ t ≤ q i) := by
  classical
  by_cases hit : ∃ i, p i = x
  · obtain ⟨i,rfl⟩ := hit
    exact ⟨q i,fun j => ⟨order j i,order i j⟩⟩
  let a := (Finset.univ.filter fun i => p i < x).image q
  let b := (Finset.univ.filter fun i => x < p i).image q
  obtain ⟨t,lo,hi⟩ := between_finsets a b (by
    rintro _ h _ h'
    obtain ⟨i,mem,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨j,mem',rfl⟩ := Finset.mem_image.mp h'
    have hlt := ((Finset.mem_filter.mp mem).2).trans (Finset.mem_filter.mp mem').2
    exact lt_of_not_ge fun h => hlt.not_ge ((order j i).mpr h))
  refine ⟨t,fun i => ?_⟩
  rcases lt_or_gt_of_ne (show p i ≠ x from fun h => hit ⟨i,h⟩) with l|r
  · have lt := lo _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,l⟩))
    exact ⟨iff_of_true l.le lt.le,iff_of_false l.not_ge lt.not_ge⟩
  · have gt := hi _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,r⟩))
    exact ⟨iff_of_false r.not_ge gt.not_ge,iff_of_true r.le gt.le⟩

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

def linearTest {I : Type*} [Fintype I] (a : I → F) (x : I → V) : V := ∑ i, a i • x i

def SameSign {A B : Type*} [Zero A] [Zero B] [LE A] [LE B] (a : A) (b : B) :=
  (0 ≤ a ↔ 0 ≤ b) ∧ (a ≤ 0 ↔ b ≤ 0)

private theorem sign_smul (d : F) {a : V} {b : F} (h : SameSign a b) : SameSign (d • a) (d • b) := by
  obtain ⟨p,n⟩ := h
  constructor <;> simp only [smul_nonneg_iff,smul_nonpos_iff,p,n]

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
private theorem linearTest_scale {I : Type*} [Fintype I] (d : F) (a : I → F) (x : I → V) :
    linearTest (fun i => d*a i) x = d • linearTest a x := by simp [linearTest,Finset.smul_sum,mul_smul]

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
private theorem linearTest_sub {I : Type*} [Fintype I] (a b : I → F) (x : I → V) :
    linearTest (fun i => a i-b i) x = linearTest a x - linearTest b x := by simp [linearTest,sub_smul,Finset.sum_sub_distrib]

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
private theorem split_test {n} (a : Fin (n+1) → F) (x : Fin (n+1) → V) :
    linearTest a x = linearTest (Fin.init a) (Fin.init x) + a (Fin.last n) • x (Fin.last n) :=
  Fin.sum_univ_castSucc _

omit [LinearOrder F] [IsStrictOrderedRing F] [LinearOrder V] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
private theorem threshold_test (d : F) (ne : d ≠ 0) (b x : V) :
    b+d • x = d • (x - (-d⁻¹) • b) := by simp [smul_smul,ne,add_comm]

/-- Every finite family of linear forms admits a field-valued tuple with
all the same strict inequalities and equalities as the given value tuple. -/
theorem realize_linear_signs (n : ℕ) : ∀ {I : Type} [Fintype I] (a : I → Fin n → F) (x : Fin n → V),
    ∃ y : Fin n → F, ∀ i, SameSign (linearTest (a i) x) (linearTest (a i) y) := by
  classical
  induction n with
  | zero => intro I _ a x; exact ⟨Fin.elim0,fun _ => by simp [linearTest,SameSign]⟩
  | succ n ih =>
    intro I _ a x
    let rest (i : I) := Fin.init (a i)
    let d (i : I) := a i (Fin.last n)
    let β (i : I) (j : Fin n) := -((d i)⁻¹) * rest i j
    let tests : I ⊕ (I × I) → Fin n → F := Sum.elim rest (fun ij j => β ij.1 j - β ij.2 j)
    obtain ⟨z,sign⟩ := ih tests (Fin.init x)
    let p (i : I) := linearTest (β i) (Fin.init x)
    let q (i : I) := linearTest (β i) z
    have ordered (i j : I) : p i ≤ p j ↔ q i ≤ q j := by
      simpa only [p,q,tests,Sum.elim_inr,linearTest_sub,sub_nonpos] using (sign (.inr (i,j))).2
    obtain ⟨t,cut⟩ := transfer_cut p q ordered (x (Fin.last n))
    refine ⟨Fin.snoc z t,fun i => ?_⟩
    rw [split_test,split_test,Fin.init_snoc,Fin.snoc_last]
    change SameSign (linearTest (rest i) (Fin.init x) + d i • x (Fin.last n)) (linearTest (rest i) z + d i • t)
    by_cases h : d i=0
    · simpa [h,tests] using sign (.inl i)
    · rw [threshold_test _ h,threshold_test _ h]
      apply sign_smul
      have compare : SameSign (x (Fin.last n) - p i) (t - q i) := by
        simpa only [SameSign,sub_nonneg,sub_nonpos] using cut i
      simpa only [p,q,β,linearTest_scale] using compare

end GeneralizedEuler.Section4.Polyhedral
