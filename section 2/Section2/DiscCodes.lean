module

public import Section2.ValuativeDisc

/-! Disc codes, polydiscs, and RV hulls from §2.4. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- An open disc has nonzero multiplicative radius. A closed disc of
radius zero represents a field point. -/
inductive DiscDescription
  | openDisc (center : K) (radius : O.ValueGroup) (nonzero : radius ≠ 0)
  | closedDisc (center : K) (radius : O.ValueGroup)

@[expose]
def DiscDescription.points : DiscDescription O → Set K
  | .openDisc c r _ => GeneralizedEuler.Section2.openDisc O c r
  | .closedDisc c r => GeneralizedEuler.Section2.closedDisc O c r

/-- Descriptions give the same disc exactly when their point sets agree. -/
def discDescriptionSetoid : Setoid (DiscDescription O) :=
  Setoid.ker (DiscDescription.points O)

abbrev DiscCode := Quotient (discDescriptionSetoid O)

/-- The field points of a disc code, independent of its center. -/
def DiscCode.points : DiscCode O → Set K :=
  Quotient.lift (DiscDescription.points O) (fun _ _ h => h)

theorem DiscCode.points_injective : Function.Injective (DiscCode.points O) := by
  intro d e
  refine Quotient.inductionOn₂ d e ?_
  intro a b h
  exact Quotient.sound h

def openDiscCode (c : K) (r : O.ValueGroup) (hr : r ≠ 0) : DiscCode O :=
  Quotient.mk _ (.openDisc c r hr)

def closedDiscCode (c : K) (r : O.ValueGroup) : DiscCode O :=
  Quotient.mk _ (.closedDisc c r)

@[simp] theorem openDiscCode_points (c : K) (r : O.ValueGroup) (hr : r ≠ 0) :
    DiscCode.points O (openDiscCode O c r hr) = openDisc O c r := by rfl

@[simp] theorem closedDiscCode_points (c : K) (r : O.ValueGroup) :
    DiscCode.points O (closedDiscCode O c r) = closedDisc O c r := by rfl

theorem openDiscCode_change_center {c d : K} {r : O.ValueGroup} (hr : r ≠ 0)
    (hd : d ∈ openDisc O c r) : openDiscCode O d r hr = openDiscCode O c r hr := by
  apply DiscCode.points_injective O
  rw [openDiscCode_points, openDiscCode_points, openDisc_change_center O hd]

theorem closedDiscCode_change_center {c d : K} {r : O.ValueGroup}
    (hd : d ∈ closedDisc O c r) : closedDiscCode O d r = closedDiscCode O c r := by
  apply DiscCode.points_injective O
  rw [closedDiscCode_points, closedDiscCode_points, closedDisc_change_center O hd]

theorem closedDiscCode_zero_points (c : K) :
    DiscCode.points O (closedDiscCode O c 0) = {c} := by
  rw [closedDiscCode_points]
  ext x
  change O.valuation (x - c) ≤ 0 ↔ x = c
  rw [nonpos_iff_eq_zero, map_eq_zero, sub_eq_zero]

theorem closedDiscCode_zero_injective : Function.Injective (fun c : K => closedDiscCode O c 0) := by
  intro x y h
  have he := congrArg (DiscCode.points O) h
  rw [closedDiscCode_zero_points, closedDiscCode_zero_points] at he
  exact Set.singleton_injective he

/-- Two discs meeting in any field point are nested. -/
theorem DiscCode.nested_of_mem_both {D E : DiscCode O} {b : K}
    (hD : b ∈ DiscCode.points O D) (hE : b ∈ DiscCode.points O E) :
    DiscCode.points O D ⊆ DiscCode.points O E ∨ DiscCode.points O E ⊆ DiscCode.points O D := by
  revert hD hE
  refine Quotient.inductionOn₂ D E ?_
  intro d e
  have theOpen {c : K} {r : O.ValueGroup} (hb : b ∈ openDisc O c r) :
      openDisc O c r = openDisc O b r := (openDisc_change_center O hb).symm
  have theClosed {c : K} {r : O.ValueGroup} (hb : b ∈ closedDisc O c r) :
      closedDisc O c r = closedDisc O b r := (closedDisc_change_center O hb).symm
  have open_mono {r s : O.ValueGroup} (h : r ≤ s) : openDisc O b r ⊆ openDisc O b s :=
    fun _ hx => lt_of_lt_of_le hx h
  have closed_mono {r s : O.ValueGroup} (h : r ≤ s) : closedDisc O b r ⊆ closedDisc O b s := by
    intro x hx
    change O.valuation (x - b) ≤ s
    exact le_trans hx h
  have nested_open_closed (r s : O.ValueGroup) :
      openDisc O b r ⊆ closedDisc O b s ∨ closedDisc O b s ⊆ openDisc O b r := by
    rcases le_or_gt r s with h | h
    · exact Or.inl ((openDisc_subset_closedDisc O).trans (closed_mono h))
    · exact Or.inr (fun _ hx => lt_of_le_of_lt hx h)
  cases d with
  | openDisc c r hr =>
    cases e with
    | openDisc d s hs =>
      intro hc hd
      change b ∈ openDisc O c r at hc
      change b ∈ openDisc O d s at hd
      change openDisc O c r ⊆ openDisc O d s ∨ openDisc O d s ⊆ openDisc O c r
      rw [theOpen hc, theOpen hd]
      exact (le_total r s).imp open_mono open_mono
    | closedDisc d s =>
      intro hc hd
      change b ∈ openDisc O c r at hc
      change b ∈ closedDisc O d s at hd
      change openDisc O c r ⊆ closedDisc O d s ∨ closedDisc O d s ⊆ openDisc O c r
      rw [theOpen hc, theClosed hd]
      exact nested_open_closed r s
  | closedDisc c r =>
    cases e with
    | openDisc d s hs =>
      intro hc hd
      change b ∈ closedDisc O c r at hc
      change b ∈ openDisc O d s at hd
      change closedDisc O c r ⊆ openDisc O d s ∨ openDisc O d s ⊆ closedDisc O c r
      rw [theClosed hc, theOpen hd]
      exact (nested_open_closed s r).symm
    | closedDisc d s =>
      intro hc hd
      change b ∈ closedDisc O c r at hc
      change b ∈ closedDisc O d s at hd
      change closedDisc O c r ⊆ closedDisc O d s ∨ closedDisc O d s ⊆ closedDisc O c r
      rw [theClosed hc, theClosed hd]
      exact (le_total r s).imp closed_mono closed_mono

/-- A disc avoiding zero lies in one nonzero RV fiber. -/
theorem DiscCode.exists_rv_fiber_of_zero_not_mem (D : DiscCode O)
    (h : 0 ∉ DiscCode.points O D) :
    ∃ t : RV0 O, t ≠ 0 ∧ DiscCode.points O D ⊆ (rv O) ⁻¹' {t} := by
  revert h
  refine Quotient.inductionOn D ?_
  intro d h
  cases d with
  | openDisc c r hr =>
    change 0 ∉ openDisc O c r at h
    have hc : c ≠ 0 := fun he => h (he ▸ mem_openDisc_center O hr c)
    have hval : r ≤ O.valuation c := by
      apply le_of_not_gt
      simpa only [openDisc, Set.mem_ofPred_eq, zero_sub, O.valuation.map_neg] using h
    refine ⟨rv O c, (rv_eq_zero_iff O).not.mpr hc, fun x hx => ?_⟩
    exact (rv_eq_rv_iff_valuation O hc).mpr (lt_of_lt_of_le hx hval)
  | closedDisc c r =>
    change 0 ∉ closedDisc O c r at h
    have hc : c ≠ 0 := fun he => h (he ▸ mem_closedDisc_center O r c)
    have hval : r < O.valuation c := by
      apply lt_of_not_ge
      simpa only [closedDisc, Set.mem_ofPred_eq, zero_sub, O.valuation.map_neg] using h
    refine ⟨rv O c, (rv_eq_zero_iff O).not.mpr hc, fun x hx => ?_⟩
    exact (rv_eq_rv_iff_valuation O hc).mpr (lt_of_le_of_lt hx hval)

/-- Constant unsigned valuation characterizes discs avoiding zero
together with the singleton at zero. -/
theorem DiscCode.valuation_constant_iff (D : DiscCode O) :
    (∃ r, ∀ x ∈ DiscCode.points O D, O.valuation x = r) ↔
      0 ∉ DiscCode.points O D ∨ DiscCode.points O D = {0} := by
  constructor
  · rintro ⟨r, hr⟩
    by_cases h0 : 0 ∈ DiscCode.points O D
    · right
      have hr0 : r = 0 := (hr 0 h0).symm.trans (map_zero O.valuation)
      ext x
      exact ⟨fun hx => (map_eq_zero O.valuation).mp ((hr x hx).trans hr0),
        fun he => (Set.mem_singleton_iff.mp he).symm ▸ h0⟩
    · exact Or.inl h0
  · rintro (h | h)
    · obtain ⟨t, _, ht⟩ := DiscCode.exists_rv_fiber_of_zero_not_mem O D h
      refine ⟨unsignedValue O t, fun x hx => ?_⟩
      have he : rv O x = t := ht hx
      exact (unsignedValue_rv O x).symm.trans (congrArg (unsignedValue O) he)
    · rw [h]
      exact ⟨0, fun _ hx => (Set.mem_singleton_iff.mp hx).symm ▸ map_zero O.valuation⟩

def DiscDescription.radius : DiscDescription O → O.ValueGroup
  | .openDisc _ r _ => r
  | .closedDisc _ r => r

/-- A thin annulus removes the maximal open child through the chosen
point of the closed disc. -/
def thinAnnulus (c b : K) (r : O.ValueGroup) : Set K :=
  closedDisc O c r \ openDisc O b r

variable {I J : Type*}

/-- A product of field discs with a fixed tuple in RV. -/
def fieldRVPolydisc (D : I → Set K) (t : J → RV0 O) :
    Set ((I → K) × (J → RV0 O)) :=
  {x | (∀ i, x.1 i ∈ D i) ∧ x.2 = t}

/-- The disc descriptions of the field coordinates and the fixed RV tuple. -/
structure PolydiscDescription (I J : Type*) where
  discs : I → DiscDescription O
  auxiliary : J → RV0 O

def PolydiscDescription.points (D : PolydiscDescription O I J) : Set ((I → K) × (J → RV0 O)) :=
  fieldRVPolydisc O (fun i => DiscDescription.points O (D.discs i)) D.auxiliary

def PolydiscDescription.polyradius (D : PolydiscDescription O I J) : I → O.ValueGroup :=
  fun i => DiscDescription.radius O (D.discs i)

/-- The largest multiplicative bound is the smallest valuative radius
in the manuscript's additive order. -/
def PolydiscDescription.radius [Fintype I] (D : PolydiscDescription O I J) : O.ValueGroup :=
  Finset.univ.sup (PolydiscDescription.polyradius O D)

def PolydiscDescription.IsBall (D : PolydiscDescription O I J) : Prop :=
  ∀ i j, PolydiscDescription.polyradius O D i = PolydiscDescription.polyradius O D j

def openPolydisc (c : I → K) (r : I → O.ValueGroup) (t : J → RV0 O) :
    Set ((I → K) × (J → RV0 O)) :=
  fieldRVPolydisc O (fun i => openDisc O (c i) (r i)) t

def closedPolydisc (c : I → K) (r : I → O.ValueGroup) (t : J → RV0 O) :
    Set ((I → K) × (J → RV0 O)) :=
  fieldRVPolydisc O (fun i => closedDisc O (c i) (r i)) t

def rvPolydisc (s : I → RV0 O) (t : J → RV0 O) : Set ((I → K) × (J → RV0 O)) :=
  fieldRVPolydisc O (fun i => (rv O) ⁻¹' {s i}) t

/-- The simultaneous leading-term map on the field coordinates, with
the auxiliary coordinates kept. -/
@[expose]
def polydiscRVMap (x : (I → K) × (J → RV0 O)) : (I → RV0 O) × (J → RV0 O) :=
  (rv O ∘ x.1, x.2)

theorem rvPolydisc_eq_fiber (s : I → RV0 O) (t : J → RV0 O) :
    rvPolydisc O s t = polydiscRVMap O ⁻¹' {(s, t)} := by
  ext x
  change (∀ i, rv O (x.1 i) = s i) ∧ x.2 = t ↔ polydiscRVMap O x = (s, t)
  exact ⟨fun h => Prod.ext (funext h.1) h.2,
    fun h => ⟨congrFun (congrArg Prod.fst h), congrArg Prod.snd h⟩⟩

/-- The union of all RV-polydiscs meeting the set. -/
@[expose]
def rvHull (S : Set ((I → K) × (J → RV0 O))) : Set ((I → K) × (J → RV0 O)) :=
  polydiscRVMap O ⁻¹' (polydiscRVMap O '' S)

theorem rvHull_eq_union_polydiscs (S : Set ((I → K) × (J → RV0 O))) :
    rvHull O S = ⋃ x ∈ S, rvPolydisc O (rv O ∘ x.1) x.2 := by
  ext x
  simp only [rvHull, Set.mem_preimage, Set.mem_image, Set.mem_iUnion, rvPolydisc_eq_fiber,
    Set.mem_singleton_iff]
  refine exists_congr fun y => ?_
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun ⟨h, he⟩ => ⟨h, he.symm⟩⟩

theorem subset_rvHull (S : Set ((I → K) × (J → RV0 O))) : S ⊆ rvHull O S :=
  fun _ hx => ⟨_, hx, rfl⟩

theorem rvHull_monotone : Monotone (rvHull O (I := I) (J := J)) :=
  fun _ _ h => Set.preimage_mono (Set.image_mono h)

@[simp] theorem rvHull_idem (S : Set ((I → K) × (J → RV0 O))) :
    rvHull O (rvHull O S) = rvHull O S := by
  apply le_antisymm
  · rintro x ⟨y, hy, he⟩
    obtain ⟨z, hz, h⟩ := hy
    exact ⟨z, hz, h.trans he⟩
  · exact subset_rvHull O _

/-- A set is an RV pullback exactly when it is the inverse image
of a set in the RV coordinates. -/
theorem rvHull_eq_self_iff (S : Set ((I → K) × (J → RV0 O))) :
    rvHull O S = S ↔ ∃ A : Set ((I → RV0 O) × (J → RV0 O)), S = polydiscRVMap O ⁻¹' A := by
  constructor
  · intro h
    exact ⟨polydiscRVMap O '' S, h.symm⟩
  · rintro ⟨A, rfl⟩
    apply le_antisymm
    · rintro _ ⟨y, hy, he⟩
      change polydiscRVMap O y ∈ A at hy
      change polydiscRVMap O _ ∈ A
      exact he ▸ hy
    · exact subset_rvHull O _

end GeneralizedEuler.Section2
