module

public import Section3.ConvexCuts
import all Section2.WeakOminimal
public import Mathlib.Data.Finset.Lattice.Fold

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 Set

variable {G : Type*} [LinearOrder G] [DenselyOrdered G]

/-- A finite cover by convex sets is constant on some interval immediately
to the right of a finite endpoint. No completeness of the order is used. -/
theorem exists_initial_interval_in_piece {I : Type*} [Fintype I] (C : I → Set G)
    (hc : ∀ i, (C i).OrdConnected) {r s : G} (hrs : r < s)
    (hcover : Ioo r s ⊆ ⋃ i, C i) : ∃ i, ∃ b > r, Ioo r b ⊆ C i := by
  classical
  obtain ⟨x,hrx,hxs⟩ := exists_between hrs
  obtain ⟨j,_⟩ := mem_iUnion.mp (hcover ⟨hrx,hxs⟩)
  have : Nonempty I := ⟨j⟩
  have hco : ∃ i, ∀ b > r, ∃ x ∈ Ioo r b, x ∈ C i := by
    by_contra! h
    choose b hb hbad using h
    let F := Finset.univ.image b
    have hF : F.Nonempty := Finset.univ_nonempty.image b
    let m := F.min' hF
    have hm : r < m := by
      obtain ⟨i,_,he⟩ := Finset.mem_image.mp (F.min'_mem hF)
      exact (hb i).trans_eq he
    obtain ⟨y,hry,hy⟩ := exists_between (lt_min hm hrs)
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover ⟨hry,(lt_min_iff.mp hy).2⟩)
    exact hbad i y ⟨hry, (lt_min_iff.mp hy).1.trans_le
      (F.min'_le _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))⟩ hi
  obtain ⟨i,hi⟩ := hco
  obtain ⟨b,hb,hbc⟩ := hi s hrs
  refine ⟨i,b,hb.1,?_⟩
  rintro y ⟨hry,hyb⟩
  obtain ⟨z,hz,hzc⟩ := hi y hry
  exact (hc i).out hzc hbc ⟨hz.2.le,hyb.le⟩

/-- The value-sort stabilization in 3.9. Orthogonality supplies the finite
range. O-minimality supplies the convex decompositions of its fibers. -/
theorem finite_range_germ {R : Type*} {r s : G} (hrs : r < s) (f : G → R)
    (hf : (f '' Ioo r s).Finite)
    (hc : ∀ v ∈ f '' Ioo r s, FiniteConvexUnion {t ∈ Ioo r s | f t = v}) :
    ∃ v, ∃ b > r, ∀ t ∈ Ioo r b, f t = v := by
  classical
  let U := f '' Ioo r s
  let : Fintype U := hf.fintype
  choose n C hconv hcov using fun v : U => hc v.val v.property
  let cells (p : Σ v : U, Fin (n v)) := C p.1 p.2
  have cover : Ioo r s ⊆ ⋃ i, cells i := by
    intro t ht
    let v : U := ⟨f t,mem_image_of_mem f ht⟩
    have hm : t ∈ {u ∈ Ioo r s | f u = v.val} := ⟨ht,rfl⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcov v ▸ hm)
    exact mem_iUnion.mpr ⟨⟨v,j⟩,hj⟩
  obtain ⟨⟨v,j⟩,b,hb,h⟩ := exists_initial_interval_in_piece cells
    (fun ⟨v,j⟩ => hconv v j) hrs cover
  refine ⟨v,b,hb,fun t ht => ?_⟩
  have hu : t ∈ ⋃ j, C v j := mem_iUnion.mpr ⟨j,h ht⟩
  exact (show t ∈ {u ∈ Ioo r s | f u = v.val} from (hcov v).symm ▸ hu).2

/-- Two-sided conclusion of 3.9 in shell coordinates centered at the
chosen field point. The exceptional labels are finite by finite_cutLabels.
Each sign can have a different eventual residue. The inner boundary shell
is included in the conclusion. -/
theorem stabilize_two_ends {X R : Type*} (f : X → R) (val : X → G) (sign : X → Bool)
    (sel : Bool → G → R) (r s : G) (hrs : r < s)
    (hfin : ∀ b, (sel b '' Ioo r s).Finite)
    (htame : ∀ b v, v ∈ sel b '' Ioo r s → FiniteConvexUnion {t ∈ Ioo r s | sel b t = v})
    (exc : Finset G) (hagree : ∀ x, val x ∈ Ioo r s → val x ∉ exc →
      f x = sel (sign x) (val x)) :
    ∃ β ∈ Ioo r s, ∃ out : Bool → R,
      ∀ x, r < val x → val x ≤ β → f x = out (sign x) := by
  classical
  choose out b hb hg using fun side => finite_range_germ hrs (sel side) (hfin side) (htame side)
  let finiteBounds := insert s (insert (b true) (insert (b false) (exc.filter (r < ·))))
  have hne : finiteBounds.Nonempty := ⟨s,Finset.mem_insert_self ..⟩
  let m := finiteBounds.min' hne
  have hmin : r < m := by
    have hm := finiteBounds.min'_mem hne
    simp only [finiteBounds,Finset.mem_insert,Finset.mem_filter] at hm
    rcases hm with h | h | h | ⟨_,h⟩
    · exact hrs.trans_eq h.symm
    · exact (hb true).trans_eq h.symm
    · exact (hb false).trans_eq h.symm
    · exact h
  obtain ⟨β,hrβ,hβm⟩ := exists_between hmin
  have hβ (t : G) (ht : t ∈ finiteBounds) : β < t :=
    hβm.trans_le (finiteBounds.min'_le t ht)
  have hβs := hβ s (Finset.mem_insert_self ..)
  refine ⟨β,⟨hrβ,hβs⟩,out,?_⟩
  intro x hrx hxb
  have he : val x ∉ exc := fun hx => (hβ (val x) (by simp [finiteBounds,hx,hrx])).not_ge hxb
  have hbs : β < b (sign x) := hβ _ (by cases sign x <;> simp [finiteBounds])
  exact (hagree x ⟨hrx,hxb.trans_lt hβs⟩ he).trans (hg _ _ ⟨hrx,hxb.trans_lt hbs⟩)

end GeneralizedEuler.Section3
