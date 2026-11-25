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
