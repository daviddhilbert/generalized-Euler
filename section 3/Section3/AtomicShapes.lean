module

public import Section3.AtomicIntervals
public import Section2.DiscCodes
public import Section2.DefinableEndDiscs

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (O : ValuationSubring K) (hO : IsOrderConvex O)

/-- The two halves of a thin annulus: the child is excluded, its closed
parent is included. -/
def annulusSide (upper : Bool) (inner outer : Set K) : Set K :=
  if upper then valuativeInterval (some ⟨inner,false⟩) (some ⟨outer,true⟩)
  else valuativeInterval (some ⟨outer,true⟩) (some ⟨inner,false⟩)

/-- The four unary shapes of Remark 3.11, with singletons included in
the first disjunct via IsEndDisc. -/
def IsAtomicShape (A : Set K) : Prop :=
  IsEndDisc O A ∨ ∃ a r, r ≠ 0 ∧ ∃ upper, A = annulusSide upper (openDisc O a r) (closedDisc O a r)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem endDisc_tagged_at {A : Set K} (hA : IsEndDisc O A) {a : K} (ha : a ∈ A) :
    ∃ b r, A = taggedDisc O b a r := by
  rcases hA with ⟨c,rfl⟩ | ⟨c,r,hr,rfl | rfl⟩
  · rw [mem_singleton_iff] at ha
    subst a
    exact ⟨true,0,by rw [taggedDisc,ite_eq_left rfl,←closedDiscCode_points]; exact (closedDiscCode_zero_points O c).symm⟩
  · exact ⟨false,r,(openDisc_change_center O ha).symm⟩
  · exact ⟨true,r,(closedDisc_change_center O ha).symm⟩

include hO in
private theorem endDisc_connected {A : Set K} (hA : IsEndDisc O A) : A.OrdConnected := by
  obtain ⟨c,H,hH,rfl⟩ := hA.exists_convexAddSubgroup O hO
  exact ⟨fun {_} hx {_} hy _ hz => hH.out hx hy ⟨sub_le_sub_right hz.1 c,sub_le_sub_right hz.2 c⟩⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem taggedDisc_reflect (b : Bool) (a : K) (r : O.ValueGroup) (x : K) :
    x ∈ taggedDisc O b a r ↔ 2*a-x ∈ taggedDisc O b a r := by
  have h : 2*a-x-a = -(x-a) := by ring
  cases b <;> simp only [taggedDisc,Bool.false_eq_true,ite_false,ite_true,openDisc,closedDisc,
    mem_ofPred_eq,h,O.valuation.map_neg]

include hO in
/-- A nested excluded end producing an atomic side must be the open
child of a closed parent. The separating test names the intermediate
radius, but quantifies its center inside the already definable inner end. -/
theorem atomic_nested_side [DenselyOrdered O.ValueGroup]
    {F : Set (Set K)} {L R : Set K} (hL : IsEndDisc O L) (hR : IsEndDisc O R)
    (hlr : L ⊂ R) (upper : Bool) (atom : GeneratesType F (annulusSide upper L R))
    (test : ∀ t, {x | ∃ a ∈ L, x ∈ openDisc O a t} ∈ F) :
    IsAtomicShape O (annulusSide upper L R) := by
  have hLne : L.Nonempty := by
    rcases hL with ⟨c,rfl⟩ | ⟨c,r,hr,rfl | rfl⟩
    · exact ⟨_,rfl⟩
    · exact ⟨_,mem_openDisc_center O hr c⟩
    · exact ⟨_,mem_closedDisc_center O r c⟩
  obtain ⟨a,ha⟩ := hLne
  obtain ⟨b,r,hinner⟩ := endDisc_tagged_at O hL ha
  obtain ⟨d,s,houter⟩ := endDisc_tagged_at O hR (hlr.subset ha)
  have h := hlr
  rw [hinner,houter] at h
  rcases nested_disc_eq_child_or_intermediate O b d a h with ⟨rfl,rfl,rfl⟩ | ⟨t,hrt,_,hLM,hMR⟩
  · have hr : r ≠ 0 := by
      rw [hinner] at ha
      exact (zero_le.trans_lt (show O.valuation (a-a) < r from ha)).ne'
    exact Or.inr ⟨a,r,hr,upper,by rw [hinner,houter]; rfl⟩
  · rw [←hinner] at hLM
    rw [←houter] at hMR
    let M := openDisc O a t
    have ht : {x | ∃ z ∈ L, x ∈ openDisc O z t} = M := by
      ext x
      refine ⟨?_,fun hx => ⟨a,ha,hx⟩⟩
      rintro ⟨z,hz,hx⟩
      rwa [openDisc_change_center O (hLM.subset hz)] at hx
    have hM : M ∈ F := ht ▸ test t
    have hMc : M.OrdConnected := endDisc_connected O hO
      (Or.inr ⟨a,t,(zero_le.trans_lt hrt).ne',Or.inl rfl⟩)
    have splits := intermediate_disc_splits_sides ha (endDisc_connected O hO hL) hMc hLM hMR
      (by rw [hinner]; exact taggedDisc_reflect O b a r)
      (taggedDisc_reflect O false a t) (by rw [houter]; exact taggedDisc_reflect O d a s)
    have mixed : (annulusSide upper L R ∩ M).Nonempty ∧ (annulusSide upper L R \ M).Nonempty := by
      cases upper
      · exact splits.2.2
      · exact ⟨splits.1,splits.2.1⟩
    obtain ⟨⟨x,hx,hxm⟩,y,hy,hym⟩ := mixed
    exact (hym ((atom.uniform M hM x hx y hy).mp hxm)).elim

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem endDisc_nonempty {A : Set K} (h : IsEndDisc O A) : A.Nonempty := by
  rcases h with ⟨a,rfl⟩ | ⟨a,r,hr,rfl | rfl⟩
  · exact ⟨_,rfl⟩
  · exact ⟨_,mem_openDisc_center O hr a⟩
  · exact ⟨_,mem_closedDisc_center O r a⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem endDisc_code {A : Set K} (h : IsEndDisc O A) :
    ∃ d : DiscCode O, d.points O = A := by
  rcases h with ⟨a,rfl⟩ | ⟨a,r,hr,rfl | rfl⟩
  · exact ⟨_,closedDiscCode_zero_points O a⟩
  · exact ⟨_,openDiscCode_points O a r hr⟩
  · exact ⟨_,closedDiscCode_points O a r⟩

include hO in
/-- The four cases in 3.11 for bounded Holly intervals. The hypotheses on
tests specify exactly the predicates used over the base, with a single
extra value parameter for an intermediate disc as allowed by 3.12. -/
theorem atomic_shape_of_bounded_ends [DenselyOrdered O.ValueGroup] {F : Set (Set K)}
    {L R : Set K} (hL : IsEndDisc O L) (hR : IsEndDisc O R) (l r : Bool)
    (atom : GeneratesType F (valuativeInterval (some ⟨L,l⟩) (some ⟨R,r⟩)))
    (defL : L ∈ F) (defR : R ∈ F)
    (mid : {x | ∃ y ∈ L, ∃ z ∈ R, 2*x < y+z} ∈ F)
    (growL : ∀ t, {x | ∃ a ∈ L, x ∈ openDisc O a t} ∈ F)
    (growR : ∀ t, {x | ∃ a ∈ R, x ∈ openDisc O a t} ∈ F) :
    IsAtomicShape O (valuativeInterval (some ⟨L,l⟩) (some ⟨R,r⟩)) := by
  obtain ⟨a,hal,har⟩ := atom.nonempty
  obtain ⟨u,hu⟩ := endDisc_nonempty O hL
  obtain ⟨v,hv⟩ := endDisc_nonempty O hR
  by_cases hits : (L ∩ R).Nonempty
  · obtain ⟨z,hzL,hzR⟩ := hits
    obtain ⟨C,hC⟩ := endDisc_code O hL
    obtain ⟨D,hD⟩ := endDisc_code O hR
    have nested := DiscCode.nested_of_mem_both O (hC ▸ hzL) (hD ▸ hzR)
    rw [hC,hD] at nested
    cases l <;> cases r
    · exact ((hal z hzL).asymm (har z hzR)).elim
    · obtain ⟨y,hy,hay⟩ := har
      have hn : ¬ R ⊆ L := fun h => (hal y (h hy)).not_ge hay
      exact atomic_nested_side O hO hL hR ⟨nested.resolve_right hn,hn⟩ true atom growL
    · obtain ⟨x,hx,hxa⟩ := hal
      have hn : ¬ L ⊆ R := fun h => (har x (h hx)).not_ge hxa
      exact atomic_nested_side O hO hR hL ⟨nested.resolve_left hn,hn⟩ false atom growR
    · rcases atomic_included_nested_end nested ⟨u,hu⟩ ⟨v,hv⟩ defL defR atom with he | he
      · exact Or.inl (he.symm ▸ hL)
      · exact Or.inl (he.symm ▸ hR)
  · have below : ∃ x ∈ L, x ≤ a := by
      cases l
      · exact ⟨u,hu,(hal u hu).le⟩
      · exact hal
    have above : ∃ y ∈ R, a ≤ y := by
      cases r
      · exact ⟨v,hv,(har v hv).le⟩
      · exact har
    obtain ⟨x,hx,hxa⟩ := below
    obtain ⟨y,hy,hay⟩ := above
    have ordered (w) (hw : w ∈ L) (q) (hq : q ∈ R) : w < q := by
      by_contra! hqw
      rcases le_total x q with hxq | hqx
      · exact hits ⟨q,(endDisc_connected O hO hL).out hx hw ⟨hxq,hqw⟩,hq⟩
      · exact hits ⟨x,hx,(endDisc_connected O hO hR).out hq hy ⟨hqx,hxa.trans hay⟩⟩
    obtain ⟨⟨p,hp,hcut⟩,q,hq,hn⟩ := disjoint_end_midpoint_splits O hO hL hR ordered hu hv l r
    exact (hn ((atom.uniform _ mid p hp q hq).mp hcut)).elim

include hO in
/-- Constancy of the unsigned value on an atom bounds it on both
sides in the field order. Thus neither Holly end can be infinite. -/
theorem atomic_interval_has_finite_ends [NoMaxOrder O.ValueGroup] {F : Set (Set K)}
    (lo hi : Option (ValuativeIntervalEnd (K := K)))
    (atom : GeneratesType F (valuativeInterval lo hi))
    (test : ∀ r, {x | O.valuation x = r} ∈ F) :
    lo.isSome = true ∧ hi.isSome = true := by
  let I := valuativeInterval lo hi
  obtain ⟨x,hx⟩ := atom.nonempty
  obtain ⟨s,hs⟩ := exists_gt (O.valuation x)
  obtain ⟨d,hd⟩ := O.valuation_surjective s
  have bound {y : K} (hy : y ∈ I) : |y| < |d| := by
    have he : O.valuation y = O.valuation x := (atom.uniform _ (test _) x hx y hy).mp rfl
    by_contra! h
    exact hs.not_ge ((hd ▸ he ▸ valuation_le_of_abs_le_abs O hO h))
  constructor
  · cases h : lo with
    | some _ => rfl
    | none =>
      have ray := upperClosure_valuativeInterval atom.nonempty
      have hm : -|d| ∈ {y | allowedAbove lo y} := by rw [h]; trivial
      obtain ⟨y,hy,hyl⟩ := ray ▸ hm
      exact ((abs_lt.mp (bound hy)).1.not_ge hyl).elim
  · cases h : hi with
    | some _ => rfl
    | none =>
      have ray := lowerClosure_valuativeInterval atom.nonempty
      have hm : |d| ∈ {y | allowedBelow hi y} := by rw [h]; trivial
      obtain ⟨y,hy,hyl⟩ := ray ▸ hm
      exact ((abs_lt.mp (bound hy)).2.not_ge hyl).elim

open FirstOrder

include hO in
/-- Remark 3.11 from HNF and the fixed-base definability of the tests.
The atom remains uniform for the value-parameter tests by 3.12.
Its two end discs are recovered from the interval over the original base. -/
theorem atomic_shape_of_holly [DenselyOrdered O.ValueGroup] [NoMaxOrder O.ValueGroup]
    {J : Language} [J.Structure K] {T : OrderedFieldTerms J}
    (hT : InterpretsOrderedFieldTerms (A := K) T) {P U : Set K}
    (atom : AtomicOver {D | P.Definable₁ J D} U) {pieces : Finset (Set K)}
    (hnf : IsHollyDecomposition O U pieces)
    (tests : Set (Set K)) (uniform : GeneratesType tests U)
    (base : ∀ D, P.Definable₁ J D → D ∈ tests)
    (values : ∀ r, {x | O.valuation x = r} ∈ tests)
    (mid : ∀ L R, P.Definable₁ J L → P.Definable₁ J R →
      {x | ∃ y ∈ L, ∃ z ∈ R, 2*x < y+z} ∈ tests)
    (grow : ∀ D, P.Definable₁ J D → ∀ r, {x | ∃ a ∈ D, x ∈ openDisc O a r} ∈ tests) :
    IsAtomicShape O U := by
  obtain ⟨hne,lo,hi,hl,hr,rfl⟩ := atomic_is_valuativeInterval O atom hnf
    (definable_firstComponent T.le hT.le atom.1)
  obtain ⟨low,high⟩ := atomic_interval_has_finite_ends O hO lo hi uniform values
  cases lo with
  | none => contradiction
  | some l =>
    cases hi with
    | none => contradiction
    | some r =>
      have hL := hl l rfl
      have hR := hr r rfl
      have dL := definable₁_leftEndDisc O hO hT hL hne atom.1
      have dR := definable₁_rightEndDisc O hO hT hR hne atom.1
      exact atomic_shape_of_bounded_ends O hO hL hR l.included r.included uniform
        (base _ dL) (base _ dR) (mid _ _ dL dR) (grow _ dL) (grow _ dR)

end GeneralizedEuler.Section3
