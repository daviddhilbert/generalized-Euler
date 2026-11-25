module

public import Section3.DiscMaps
public import Section3.PolydiscImages
import all Section3.PolydiscImages

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K) [DenselyOrdered O.ValueGroup]

theorem openDisc_nontrivial (c : K) {r : O.ValueGroup} (hr : r ≠ 0) : (openDisc O c r).Nontrivial := by
  obtain ⟨s,hs,hsr⟩ := exists_between (pos_iff_ne_zero.mpr hr)
  obtain ⟨u,hu⟩ := O.valuation_surjective s
  have un : u ≠ 0 := (map_ne_zero O.valuation).mp (hu.trans_ne hs.ne')
  refine ⟨u+c,?_,c,mem_openDisc_center O hr c,by simpa using un⟩
  change O.valuation (u+c-c) < r
  simpa [hu] using hsr

private theorem concentric_of_injective {A : Set K} {f : K → K} (inj : InjOn f A)
    (shape : ∀ c r, r ≠ 0 → openDisc O c r ⊆ A → IsPointOrOpen O (f '' openDisc O c r)) :
    ConcentricOn O A f := by
  intro c r hr sub
  rcases shape c r hr sub with ⟨z,hz⟩ | h
  · obtain ⟨x,hx,y,hy,hne⟩ := openDisc_nontrivial O c hr
    have member (a) (ha : a ∈ openDisc O c r) : f a ∈ ({z} : Set K) := hz ▸ mem_image_of_mem f ha
    exact (hne (inj (sub hx) (sub hy) ((member x hx).trans (member y hy).symm))).elim
  · exact h

/-- The common refinement for 3.24. Each source piece records both
the forward partition index and the partition index of its image. -/
theorem discToDisc_refine {A B : Set K} {f g : K → K} (bij : BijOn f A B) (inv : InvOn g f A B)
    {S T : Set K} (forward : ∀ c r, r ≠ 0 → openDisc O c r ⊆ A ∩ S → IsPointOrOpen O (f '' openDisc O c r))
    (back : ∀ c r, r ≠ 0 → openDisc O c r ⊆ B ∩ T → IsPointOrOpen O (g '' openDisc O c r)) :
    let D := (A ∩ S) ∩ f ⁻¹' T
    DiscToDiscOn O D (f '' D) f g := by
  intro D
  have sub : D ⊆ A := fun _ h => h.1.1
  have im : f '' D ⊆ B ∩ T := fun _ ⟨z,hz,he⟩ => he ▸ ⟨bij.mapsTo (sub hz),hz.2⟩
  have restr : BijOn f D (f '' D) := ⟨mapsTo_image _ _,bij.injOn.mono sub,fun _ h => h⟩
  refine ⟨restr,⟨fun _ h => inv.1 (sub h),fun _ h => inv.2 (im h).1⟩,
    concentric_of_injective O restr.injOn (fun c r hr h => forward c r hr (fun x hx => (h hx).1)),?_⟩
  apply concentric_of_injective O _ (fun c r hr h => back c r hr (h.trans im))
  intro x hx y hy he
  exact (inv.2 (im hx).1).symm.trans ((congrArg f he).trans (inv.2 (im hy).1))

/-- One field coordinate with arbitrary auxiliary input and output tags.
A single pair of finite indices works on the entire mixed domain. The
tag of the image and both indices are functions of the original input.
The final conclusion describes each actual VF-fiber of the restriction. -/
theorem mixed_discToDisc_partition {U V I J : Type*} [Finite I] [Finite J]
    (A : Set (K × U)) (B : Set (K × V)) (f : K × U → K × V) (g : K × V → K × U)
    (bij : BijOn f A B) (inv : InvOn g f A B)
    (leftIndex : K × U → I) (rightIndex : K × V → J)
    (forward : ∀ t s i c r, r ≠ 0 → openDisc O c r ⊆
      {x | (x,t) ∈ A ∧ (f (x,t)).2 = s ∧ leftIndex (x,t) = i} →
      IsPointOrOpen O ((fun x => (f (x,t)).1) '' openDisc O c r))
    (back : ∀ s t j c r, r ≠ 0 → openDisc O c r ⊆
      {y | (y,s) ∈ B ∧ (g (y,s)).2 = t ∧ rightIndex (y,s) = j} →
      IsPointOrOpen O ((fun y => (g (y,s)).1) '' openDisc O c r)) :
    let cell (i : I × J) := {a ∈ A | leftIndex a = i.1 ∧ rightIndex (f a) = i.2}
    (∀ a ∈ A, ∃! i, a ∈ cell i) ∧
    ∀ i t s, let D := {x | (x,t) ∈ cell i ∧ (f (x,t)).2 = s}
      let F := fun x => (f (x,t)).1
      DiscToDiscOn O D (F '' D) F (fun y => (g (y,s)).1) := by
  intro cell
  refine ⟨fun a ha => ⟨(leftIndex a,rightIndex (f a)),⟨ha,rfl,rfl⟩,fun _ h => Prod.ext h.2.1.symm h.2.2.symm⟩,?_⟩
  intro i t s D F
  let S := {x | (x,t) ∈ A ∧ (f (x,t)).2 = s}
  let T := {y | (y,s) ∈ B ∧ (g (y,s)).2 = t}
  let G := fun y => (g (y,s)).1
  have fp {x} (hx : x ∈ S) : f (x,t) = (F x,s) := Prod.ext rfl hx.2
  have gp {y} (hy : y ∈ T) : g (y,s) = (G y,t) := Prod.ext rfl hy.2
  have left {x} (hx : x ∈ S) : g (F x,s) = (x,t) := (fp hx) ▸ inv.1 hx.1
  have right {y} (hy : y ∈ T) : f (G y,t) = (y,s) := (gp hy) ▸ inv.2 hy.1
  have mapF {x} (hx : x ∈ S) : F x ∈ T := ⟨fp hx ▸ bij.mapsTo hx.1,congrArg Prod.snd (left hx)⟩
  have mapG {y} (hy : y ∈ T) : G y ∈ S := by
    obtain ⟨z,hz,he⟩ := bij.surjOn hy.1
    have h := he ▸ inv.1 hz
    exact ⟨gp hy ▸ (h ▸ hz),congrArg Prod.snd (right hy)⟩
  have finv : InvOn G F S T := ⟨fun _ hx => congrArg Prod.fst (left hx),fun _ hy => congrArg Prod.fst (right hy)⟩
  have fb : BijOn F S T := ⟨fun _ hx => mapF hx,finv.1.injOn,fun y hy => ⟨G y,mapG hy,finv.2 hy⟩⟩
  let P := {x | leftIndex (x,t) = i.1}
  let Q := {y | rightIndex (y,s) = i.2}
  have heq : D = (S ∩ P) ∩ F ⁻¹' Q := by
    ext x
    constructor
    · rintro ⟨⟨ha,hi,hj⟩,ht⟩
      have h : x ∈ S := ⟨ha,ht⟩
      exact ⟨⟨h,hi⟩,by change rightIndex (F x,s) = i.2; rw [←fp h]; exact hj⟩
    · rintro ⟨⟨hs,hi⟩,hj⟩
      exact ⟨⟨hs.1,hi,(fp hs).symm ▸ hj⟩,hs.2⟩
  rw [heq]
  apply discToDisc_refine O fb finv
  · intro c r hr sub
    exact forward t s i.1 c r hr (fun x hx => ⟨(sub hx).1.1,(sub hx).1.2,(sub hx).2⟩)
  · intro c r hr sub
    exact back s t i.2 c r hr (fun x hx => ⟨(sub hx).1.1,(sub hx).1.2,(sub hx).2⟩)

end GeneralizedEuler.Section3
