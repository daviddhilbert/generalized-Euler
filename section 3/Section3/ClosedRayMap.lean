module

public import Section3.ChildSemilinear
public import Section3.RayOrientation
import all Section3.DiscRayQuotient
import all Section3.AtomicProfiles
import all Section2.ValuativeDisc

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder Set

variable {K I : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
    (hO : IsOrderConvex O) [DenselyOrdered O.ValueGroup]

/-- The actual function on residue labels induced by a proposed map
from a closed disc to either half thin annulus. Its order follows from
the order of the two positive affine charts on representatives. -/
theorem closed_half_chart {c d a b : K} {r s : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (hs : s ≠ 0) (hb : O.valuation b = s) (dp : 0 < d) (bp : 0 < b) (upper : Bool)
    {f g : K → K} (hmap : DiscToDiscOn O (closedDisc O c r) (annulusSide upper (openDisc O a s) (closedDisc O a s)) f g)
    (mon : StrictMonoOn f (closedDisc O c r) ∨ StrictAntiOn f (closedDisc O c r)) :
    letI := residueLinearOrder O hO
    ∃ (h : Residue O → Residue O) (maps : MapsTo f (closedDisc O c r) (closedDisc O a s)),
      range h = (if upper then Ioi 0 else Iio 0) ∧ (StrictMono h ∨ StrictAnti h) ∧
      ∀ x : closedDisc O c r, h (childLabel O c d hr hd x) = childLabel O a b hs hb ⟨f x.val,maps x.property⟩ := by
  let := residueLinearOrder O hO
  let Z : Set (Residue O) := if upper then Ioi 0 else Iio 0
  have map : DiscToDiscOn O (childLocus O c d hr hd univ) (childLocus O a b hs hb Z) f g := by
    rw [childLocus_univ,show Z = _ from rfl,childLocus_ray O hO a b hs hb bp upper]; exact hmap
  obtain ⟨e,comm⟩ := discToDisc_child_equiv O c d a b hr hd hs hb univ Z map
  let h (u : Residue O) := (e ⟨u,trivial⟩).val
  have inj : Function.Injective h := fun _ _ he => congrArg Subtype.val (e.injective (Subtype.ext he))
  have ran : range h = Z := by
    ext z
    exact ⟨fun ⟨v,he⟩ => he ▸ (e ⟨v,trivial⟩).property,fun hz => by
      obtain ⟨u,hu⟩ := e.surjective ⟨z,hz⟩; exact ⟨u.val,congrArg Subtype.val hu⟩⟩
  have lift (x : closedDisc O c r) : x.val ∈ childLocus O c d hr hd univ :=
    ⟨x.property,trivial⟩
  have maps : MapsTo f (closedDisc O c r) (closedDisc O a s) :=
    fun x hx => (map.1.mapsTo (lift ⟨x,hx⟩)).choose
  have link (x : closedDisc O c r) : h (childLabel O c d hr hd x) =
      childLabel O a b hs hb ⟨f x.val,maps x.property⟩ := congrArg Subtype.val (comm ⟨x.val,lift x⟩)
  refine ⟨h,maps,ran,?_,link⟩
  have order {x y : closedDisc O c r} (hne : childLabel O c d hr hd x ≠ childLabel O c d hr hd y)
      (hxy : f x.val < f y.val) : h (childLabel O c d hr hd x) < h (childLabel O c d hr hd y) := by
    rw [link,link]
    apply (discChildrenChart_lt_iff O hO a b hs hb bp _ _).mpr
    refine ⟨hxy,fun same => hne (inj ?_)⟩
    rw [link,link]
    exact (childLabel_equal_iff O a b hs hb _ _).mpr same
  rcases mon with inc | dec
  · left
    intro u v uv
    obtain ⟨x,rfl⟩ := childLabel_surjective O c d hr hd u
    obtain ⟨y,rfl⟩ := childLabel_surjective O c d hr hd v
    exact order uv.ne (inc x.property y.property ((discChildrenChart_lt_iff O hO c d hr hd dp x y).mp uv).1)
  · right
    intro u v uv
    obtain ⟨x,rfl⟩ := childLabel_surjective O c d hr hd u
    obtain ⟨y,rfl⟩ := childLabel_surjective O c d hr hd v
    exact order uv.ne' (dec x.property y.property ((discChildrenChart_lt_iff O hO c d hr hd dp x y).mp uv).1)

variable {L : Language} [L.Structure (Residue O)]

/-- Data available from a base-fixing automorphism. A definable map is
equivariant, and the definable source, target parent and omitted child
are preserved. The elementary action on the residue field is included. -/
structure MarkedDiscAutomorphism (c : K) (r : O.ValueGroup) (a : K) (s : O.ValueGroup) (f : K → K) where
  fieldMap : K ≃+* K
  ordered : StrictMono fieldMap
  ring : RespectsValuationRing O O fieldMap.toRingHom
  sourceDisc : fieldMap '' closedDisc O c r = closedDisc O c r
  targetDisc : fieldMap '' closedDisc O a s = closedDisc O a s
  omitted : fieldMap a ∈ openDisc O a s
  commutes : ∀ x ∈ closedDisc O c r, fieldMap (f x) = f (fieldMap x)
  languageMap : Residue O ≃[L] Residue O
  compatible : ∀ z, languageMap z = mapResidue O O fieldMap.toRingHom ring z

/-- Impose the field symmetries on a chart actually obtained from the
disc bijection. Transitivity on the field points of the old atom yields
transitivity on the affine line without fixing a chart origin. -/
theorem no_closed_disc_to_half {c d a b : K} {r s : O.ValueGroup} (hr : r ≠ 0) (hd : O.valuation d = r)
    (hs : s ≠ 0) (hb : O.valuation b = s) (dp : 0 < d) (bp : 0 < b) (upper : Bool) {f g : K → K}
    (hmap : DiscToDiscOn O (closedDisc O c r) (annulusSide upper (openDisc O a s) (closedDisc O a s)) f g)
    (mon : StrictMonoOn f (closedDisc O c r) ∨ StrictAntiOn f (closedDisc O c r))
    (auts : I → MarkedDiscAutomorphism (L := L) O c r a s f)
    (transitive : ∀ x y : closedDisc O c r, ∃ i, (auts i).fieldMap x.val = y.val)
    (defchart : ∀ (h : Residue O → Residue O) (maps : MapsTo f (closedDisc O c r) (closedDisc O a s)),
      (∀ x : closedDisc O c r, h (childLabel O c d hr hd x) = childLabel O a b hs hb ⟨f x.val,maps x.property⟩) →
      (univ : Set (Residue O)).Definable₂ L (fieldGraph univ h)) :
    letI := residueLinearOrder O hO
    letI := residue_isOrderedRing O hO
    IsOMinimal (K := Residue O) L → IsPowerBounded (K := Residue O) L →
    ∀ {F : OrderedFieldTerms L}, InterpretsOrderedFieldTerms (A := Residue O) F → False := by
  let := residueLinearOrder O hO
  let := residue_isOrderedRing O hO
  intro hom hpb F hF
  obtain ⟨h,maps,ray,mono,link⟩ := closed_half_chart O hO hr hd hs hb dp bp upper hmap mon
  have src (i : I) := semilinear_child_label O (auts i).fieldMap (auts i).ring c d hr hd (auts i).sourceDisc
  have dst (i : I) := semilinear_child_label O (auts i).fieldMap (auts i).ring a b hs hb (auts i).targetDisc
  choose orig dir hn _ move using src
  choose shift scale sn zero act using dst
  have equiv (i : I) (u : Residue O) : h (orig i+dir i*mapResidue O O (auts i).fieldMap.toRingHom (auts i).ring u) =
      scale i*mapResidue O O (auts i).fieldMap.toRingHom (auts i).ring (h u) := by
    obtain ⟨x,rfl⟩ := childLabel_surjective O c d hr hd u
    rw [←move i x,link,link]
    let y : closedDisc O a s := ⟨f x.val,maps x.property⟩
    have he := act i y
    rw [zero i (auts i).omitted,zero_add] at he
    convert he using 1
    exact congrArg (childLabel O a b hs hb) (Subtype.ext ((auts i).commutes x x.property).symm)
  let action (i : I) : ResidueChartAction L h := {
    fieldMap := residueFieldEquiv O (auts i).fieldMap (auts i).ring
    languageMap := (auts i).languageMap
    compatible := (auts i).compatible
    increasing := mapResidue_strictMono O O _ _ hO hO (auts i).ordered
    origin := orig i
    direction := dir i
    nonzeroDirection := hn i
    targetScale := scale i
    nonzeroScale := sn i
    equivariant := equiv i }
  apply no_atomic_line_to_either_ray hom hpb hF (defchart h maps link) action _ mono
  · cases upper <;> simp_all
  · intro u v
    obtain ⟨x,rfl⟩ := childLabel_surjective O c d hr hd u
    obtain ⟨y,rfl⟩ := childLabel_surjective O c d hr hd v
    obtain ⟨i,hi⟩ := transitive x y
    exact ⟨i,(move i x).symm.trans (congrArg (childLabel O c d hr hd) (Subtype.ext hi))⟩

end GeneralizedEuler.Section3
