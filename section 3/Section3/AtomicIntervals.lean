module

public import Section3.Atomicity
public import Section2.EndDiscs
public import Section2.DefinableHolly
public import Mathlib.Data.Fintype.Lattice

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [LinearOrder K]

/-- A point in the leftmost order component has no gap below it
between itself and any earlier point of the set. -/
def firstComponent (U : Set K) : Set K :=
  {x | x ∈ U ∧ ∀ y ∈ U, ∀ z, y ≤ z → z ≤ x → z ∈ U}

/-- The test for the first component has exactly the parameters of U. -/
theorem definable_firstComponent {L : Language} [L.Structure K]
    (order : L.Relations 2) (hLE : ∀ v : Fin 2 → K, Structure.RelMap order v ↔ v 0 ≤ v 1)
    {P U : Set K} (hU : P.Definable₁ L U) : P.Definable₁ L (firstComponent U) := by
  obtain ⟨φ,hφ⟩ := hU
  let leR := (L.lhomWithConstants P).onRelation order
  let cmp (v w : Fin 1 ⊕ Fin 2) := leR.formula
    (Fin.cases (Term.var v) (fun _ => Term.var w))
  let x : Fin 1 ⊕ Fin 2 := .inl 0
  let y : Fin 1 ⊕ Fin 2 := .inr 0
  let z : Fin 1 ⊕ Fin 2 := .inr 1
  let atVar (v : Fin 1 ⊕ Fin 2) := φ.relabel (fun _ => v)
  let test := (atVar y).imp ((cmp y z).imp ((cmp z x).imp (atVar z)))
  refine ⟨φ ⊓ Formula.iAlls (Fin 2) test,?_⟩
  ext a
  have hm (b : K) : φ.Realize (fun _ => b) ↔ b ∈ U :=
    (Set.ext_iff.mp hφ (fun _ => b)).symm
  have cval (v w) (s : Fin 1 ⊕ Fin 2 → K) : (cmp v w).Realize s ↔ s v ≤ s w := by
    rw [show cmp v w = _ from rfl, Formula.realize_rel, LHom.map_onRelation (L.lhomWithConstants P),hLE]
    rfl
  change (a 0 ∈ U ∧ _) ↔ (φ ⊓ _).Realize a
  have hconst : (fun _ : Fin 1 => a 0) = a := funext (fun i => congrArg a (Fin.fin_one_eq_zero i).symm)
  have ha := hm (a 0)
  rw [hconst] at ha
  rw [Formula.realize_inf,Formula.realize_iAlls,ha]
  apply and_congr_right
  intro _
  simp only [test,atVar,Formula.realize_imp,Formula.realize_relabel,Function.comp_def,hm,cval,
    x,y,z,Sum.elim_inl,Sum.elim_inr]
  exact ⟨fun h v hb => h _ hb _,fun h b hb e hbe hea => h ![b,e] hb hbe hea⟩

theorem holly_firstComponent_nonempty [Field K] (O : ValuationSubring K)
    {U : Set K} {P : Finset (Set K)} (h : IsHollyDecomposition O U P) (hU : U.Nonempty) :
    (firstComponent U).Nonempty := by
  classical
  have cover (a : K) : a ∈ U ↔ ∃ C : P, a ∈ C.val := by
    rw [h.2.1]
    simp
  obtain ⟨b,hb⟩ := hU
  obtain ⟨B,_⟩ := (cover b).mp hb
  let : Nonempty P := ⟨B⟩
  choose rep hrep using fun C : P => (h.1 C.val C.property).1
  obtain ⟨i,hi⟩ := Finite.exists_min rep
  refine ⟨rep i,(cover _).mpr ⟨i,hrep i⟩,?_⟩
  intro y hy z hyz hzi
  obtain ⟨C,hyC⟩ := (cover _).mp hy
  have hconv : C.val.OrdConnected := by
    obtain ⟨_,lo,hi,_,_,he⟩ := h.1 C.val C.property
    rw [he]
    exact valuativeInterval_ordConnected lo hi
  exact (cover _).mpr ⟨C,hconv.out hyC (hrep C) ⟨hyz,hzi.trans (hi C)⟩⟩

/-- The first assertion of 3.11. A fixed-base formula detects gaps,
so a unary atom occupies exactly one of its Holly intervals. -/
theorem atomic_is_valuativeInterval [Field K] (O : ValuationSubring K)
    {D : Set (Set K)} {U : Set K} {P : Finset (Set K)} (h : AtomicOver D U)
    (hH : IsHollyDecomposition O U P) (hfirst : firstComponent U ∈ D) :
    IsValuativeInterval O U := by
  obtain ⟨b,hb⟩ := holly_firstComponent_nonempty O hH h.2.nonempty
  have hall (a) (ha : a ∈ U) : a ∈ firstComponent U :=
    (h.2.uniform _ hfirst b hb.1 a ha).mp hb
  have hconv : U.OrdConnected :=
    ⟨fun {a} ha {b} hb z hz => (hall b hb).2 a ha z hz.1 hz.2⟩
  have hbU := hb.1
  rw [hH.2.1] at hbU
  obtain ⟨C,hC,hbC⟩ := mem_iUnion₂.mp hbU
  have hCeq := hH.piece_eq_component O hC hbC
  have hUeq : U = C := by
    rw [hCeq]
    exact (subset_ordConnectedComponent hb.1 Subset.rfl).antisymm ordConnectedComponent_subset
  exact hUeq ▸ hH.1 C hC


/-- Open and closed descriptions of a disc sharing a chosen center.
A closed description at value zero is a singleton. -/
def taggedDisc {K : Type*} [Field K] (O : ValuationSubring K) (closed : Bool)
    (a : K) (r : O.ValueGroup) := (if closed then closedDisc else openDisc) O a r

private theorem taggedDisc_bounds {K : Type*} [Field K] (O : ValuationSubring K) (b : Bool)
    (a : K) (r : O.ValueGroup) :
    openDisc O a r ⊆ taggedDisc O b a r ∧ taggedDisc O b a r ⊆ closedDisc O a r := by
  cases b <;> simp only [taggedDisc,Bool.false_eq_true,ite_false,ite_true,Subset.rfl, true_and,
    and_true] <;> exact openDisc_subset_closedDisc O

private theorem taggedDisc_ssubset_of_lt {K : Type*} [Field K] (O : ValuationSubring K)
    [DenselyOrdered O.ValueGroup] (b d : Bool) (a : K) {r s : O.ValueGroup} (hrs : r < s) :
    taggedDisc O b a r ⊂ taggedDisc O d a s := by
  have hsub : taggedDisc O b a r ⊆ taggedDisc O d a s := fun x hx =>
    (taggedDisc_bounds O d a s).1 (((taggedDisc_bounds O b a r).2 hx : O.valuation (x-a) ≤ r).trans_lt hrs)
  refine ⟨hsub,fun hrev => ?_⟩
  obtain ⟨u,hru,hus⟩ := exists_between hrs
  obtain ⟨w,hw⟩ := O.valuation_surjective u
  have hd : O.valuation (w+a-a) = u := by rw [add_sub_cancel_right,hw]
  have hm : w+a ∈ taggedDisc O d a s := (taggedDisc_bounds O d a s).1 (hd.trans_lt hus)
  have he : O.valuation (w+a-a) ≤ r := (taggedDisc_bounds O b a r).2 (hrev hm)
  exact hru.not_ge (hd ▸ he)

/-- At equal radius the only strict inclusion is open into closed.
At distinct radii an intermediate open disc exists regardless of either
endpoint flag, including when the inner end is a singleton. -/
theorem nested_disc_eq_child_or_intermediate {K : Type*} [Field K] (O : ValuationSubring K)
    [DenselyOrdered O.ValueGroup] (b d : Bool) (a : K) {r s : O.ValueGroup}
    (h : taggedDisc O b a r ⊂ taggedDisc O d a s) :
    (r = s ∧ b = false ∧ d = true) ∨
    ∃ t, r < t ∧ t < s ∧ taggedDisc O b a r ⊂ openDisc O a t ∧
      openDisc O a t ⊂ taggedDisc O d a s := by
  rcases lt_trichotomy r s with hrs | he | hsr
  · obtain ⟨t,hrt,hts⟩ := exists_between hrs
    exact Or.inr ⟨t,hrt,hts,taggedDisc_ssubset_of_lt O b false a hrt,
      taggedDisc_ssubset_of_lt O false d a hts⟩
  · subst s
    cases b <;> cases d
    · exact (h.ne rfl).elim
    · exact Or.inl ⟨rfl,rfl,rfl⟩
    · exact (h.2 (openDisc_subset_closedDisc O)).elim
    · exact (h.ne rfl).elim
  · exact (h.2 (taggedDisc_ssubset_of_lt O d b a hsr).subset).elim

/-- If the inner end is included, its definable disc lies in the interval.
Any one of its points forces an atomic interval to equal that disc. -/
theorem atomic_included_nested_end {D : Set (Set K)} {L R : Set K}
    (nested : L ⊆ R ∨ R ⊆ L) (hL : L.Nonempty) (hR : R.Nonempty)
    (defL : L ∈ D) (defR : R ∈ D)
    (ha : GeneratesType D (valuativeInterval (some ⟨L,true⟩) (some ⟨R,true⟩))) :
    valuativeInterval (some ⟨L,true⟩) (some ⟨R,true⟩) = L ∨
    valuativeInterval (some ⟨L,true⟩) (some ⟨R,true⟩) = R := by
  let I := valuativeInterval (some ⟨L,true⟩) (some ⟨R,true⟩)
  have inside {z : K} (hz : z ∈ L) (hz' : z ∈ R) : z ∈ I :=
    ⟨⟨z,hz,le_rfl⟩,z,hz',le_rfl⟩
  rcases nested with h | h
  · obtain ⟨x,hx⟩ := hL
    have sub : L ⊆ I := fun _ hz => inside hz (h hz)
    exact Or.inl (Subset.antisymm (fun y hy => (ha.uniform L defL x (sub hx) y hy).mp hx) sub)
  · obtain ⟨x,hx⟩ := hR
    have sub : R ⊆ I := fun _ hz => inside (h hz) hz
    exact Or.inr (Subset.antisymm (fun y hy => (ha.uniform R defR x (sub hx) y hy).mp hx) sub)

private theorem positive_shell_point [Field K] [IsStrictOrderedRing K] {U V : Set K} {a : K}
    (ha : a ∈ U) (hu : U.OrdConnected) (sub : U ⊂ V)
    (symU : ∀ x, x ∈ U ↔ 2*a-x ∈ U) (symV : ∀ x, x ∈ V ↔ 2*a-x ∈ V) :
    ∃ x ∈ V, ∀ y ∈ U, y < x := by
  obtain ⟨z,hzV,hzU⟩ := Set.exists_of_ssubset sub
  have pick {x : K} (hV : x ∈ V) (hU : x ∉ U) (hax : a ≤ x) :
      ∃ x ∈ V, ∀ y ∈ U, y < x :=
    ⟨x,hV,fun y hy => lt_of_not_ge (fun hxy => hU (hu.out ha hy ⟨hax,hxy⟩))⟩
  rcases le_total a z with h | h
  · exact pick hzV hzU h
  · exact pick ((symV z).mp hzV) (fun hz => hzU ((symU z).mpr hz)) (by linarith)

/-- An intermediate concentric disc splits both sides of the annulus,
whether its outer disc is open or closed. No maximal child is required. -/
theorem intermediate_disc_splits_sides [Field K] [IsStrictOrderedRing K]
    {L M R : Set K} {a : K} (ha : a ∈ L) (hL : L.OrdConnected) (hM : M.OrdConnected)
    (hl : L ⊂ M) (hr : M ⊂ R)
    (sl : ∀ x, x ∈ L ↔ 2*a-x ∈ L) (sm : ∀ x, x ∈ M ↔ 2*a-x ∈ M)
    (sr : ∀ x, x ∈ R ↔ 2*a-x ∈ R) :
    let upper := valuativeInterval (some ⟨L,false⟩) (some ⟨R,true⟩)
    let lower := valuativeInterval (some ⟨R,true⟩) (some ⟨L,false⟩)
    (upper ∩ M).Nonempty ∧ (upper \ M).Nonempty ∧
      (lower ∩ M).Nonempty ∧ (lower \ M).Nonempty := by
  obtain ⟨x,hx,hxl⟩ := positive_shell_point ha hL hl sl sm
  obtain ⟨y,hy,hym⟩ := positive_shell_point (hl.subset ha) hM hr sm sr
  have out : y ∉ M := fun h => (hym y h).false
  have up {z : K} (hz : z ∈ R) (h : ∀ w ∈ L, w < z) :
      z ∈ valuativeInterval (some ⟨L,false⟩) (some ⟨R,true⟩) :=
    ⟨h,z,hz,le_rfl⟩
  have down {z : K} (hz : z ∈ R) (h : ∀ w ∈ L, w < z) :
      2*a-z ∈ valuativeInterval (some ⟨R,true⟩) (some ⟨L,false⟩) := by
    refine ⟨⟨_,(sr z).mp hz,le_rfl⟩,?_⟩
    intro w hw
    have := h _ ((sl w).mp hw)
    linarith
  have hyl (z) (hz : z ∈ L) := hym z (hl.subset hz)
  exact ⟨⟨x,up (hr.subset hx) hxl,hx⟩,⟨y,up hy hyl,out⟩,
    ⟨_,down (hr.subset hx) hxl,(sm x).mp hx⟩,⟨_,down hy hyl,fun h => out ((sm y).mpr h)⟩⟩

section
variable [Field K] [IsStrictOrderedRing K] (O : ValuationSubring K) (hO : IsOrderConvex O)

include hO

private theorem endDisc_affine_five {D : Set K} (hD : IsEndDisc O D) {x y : K}
    (hx : x ∈ D) (hy : y ∈ D) : 5 * (x-y)+y ∈ D := by
  obtain ⟨c,H,_,rfl⟩ := hD.exists_convexAddSubgroup O hO
  change 5 * (x-y) + y - c ∈ H
  change x-c ∈ H at hx
  change y-c ∈ H at hy
  have hsub : x-y ∈ H := by simpa using H.sub_mem hx hy
  have h := H.add_mem (H.nsmul_mem hsub 5) hy
  simpa only [nsmul_eq_mul, Nat.cast_ofNat,add_sub_assoc] using h

/-- A separating cut for disjoint end discs. Its definition only uses
the two end sets. Quarter and three-quarter points witness the split for
every choice of the two flags on the ends. -/
theorem disjoint_end_midpoint_splits {L R : Set K}
    (hL : IsEndDisc O L) (hR : IsEndDisc O R) (ordered : ∀ x ∈ L, ∀ y ∈ R, x < y)
    {l r : K} (hl : l ∈ L) (hr : r ∈ R) (left right : Bool) :
    let I := valuativeInterval (some ⟨L,left⟩) (some ⟨R,right⟩)
    let cut := {x : K | ∃ y ∈ L, ∃ z ∈ R, 2*x < y+z}
    (I ∩ cut).Nonempty ∧ (I \ cut).Nonempty := by
  intro I cut
  let a := (3*l+r)/4
  let b := (l+3*r)/4
  have hlr := ordered l hl r hr
  have hleft (y) (hy : y ∈ L) : y < a := by
    have hh := ordered _ (endDisc_affine_five O hO hL hy hl) _ hr
    dsimp [a]; linarith
  have hright (z) (hz : z ∈ R) : b < z := by
    have hh := ordered _ hl _ (endDisc_affine_five O hO hR hz hr)
    dsimp [b]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hmem (x) (hax : a ≤ x) (hxb : x ≤ b) : x ∈ I := by
    constructor
    · cases left
      · exact fun y hy => (hleft y hy).trans_le hax
      · exact ⟨l,hl,(hleft _ hl).le.trans hax⟩
    · cases right
      · exact fun z hz => hxb.trans_lt (hright z hz)
      · exact ⟨r,hr,hxb.trans (hright r hr).le⟩
  refine ⟨⟨a,hmem a le_rfl hab.le,l,hl,r,hr,?_⟩,b,hmem b hab.le le_rfl,?_⟩
  · dsimp [a]; linarith
  · rintro ⟨y,hy,z,hz,hmid⟩
    have upper := ordered l hl _ (endDisc_affine_five O hO hR hr hz)
    have low := hleft y hy
    dsimp [a,b] at *
    linarith

end

end GeneralizedEuler.Section3
