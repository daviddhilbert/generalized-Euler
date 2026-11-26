module

public import Section5.FieldClassPartitions
public import Section5.MixedLiftPresentation
public import Section5.PaddedFieldLift

/-! Prepare a VF object and cut by the support of the nonzero field
coordinates. Each part has the VF class of one RV lift. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  [TopologicalSpace K]

local notation "𝓜" => canonicalStructure (L := L) O hO power

omit [TopologicalSpace K] in
private theorem paddedLift_test {n d m : ℕ} (U : RVObject 𝓜 S d) (p : Fin d ↪ Fin n)
    (encode : Fin m ≃ Fin U.arity)
    (x : SortedAssignment (CanonicalSort O) (MixedVariables n (Fin m))) :
    x ∈ paddedLiftCarrier O hO power S U p encode ↔
      ∃ t : U.carrier, t.val ∘ encode = x .rv ∧
        (∀ j, rv O (x .vf (p j)) = U.label t j) ∧ (∀ i ∉ Set.range p, x .vf i = 0) := by
  change (∃ t : U.carrier, t.val = x .rv ∘ encode.symm ∧ U.label t =
    (canonicalStructure (L := L) O hO power).rvMap ∘ x .vf ∘ p) ∧
     (∀ i ∉ Set.range p, x .vf i = 0) ↔ _
  constructor
  · rintro ⟨⟨t,ht,hl⟩,hz⟩
    refine ⟨t,?_,?_,hz⟩
    · funext i
      have h := congrFun ht (encode i)
      simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h
    · intro i
      simpa only [Function.comp_apply,canonicalStructure_rvMap] using (congrFun hl i).symm
  · rintro ⟨t,ht,hl,hz⟩
    refine ⟨⟨t,?_,?_⟩,hz⟩
    · funext i
      have h := congrFun ht (encode.symm i)
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h
    · funext i
      rw [Function.comp_apply,canonicalStructure_rvMap]
      exact (hl i).symm

omit [TopologicalSpace K] in
private theorem paddedLift_support {n d m : ℕ} (U : RVObject 𝓜 S d) (p : Fin d ↪ Fin n)
    (encode : Fin m ≃ Fin U.arity)
    (x : SortedAssignment (CanonicalSort O) (MixedVariables n (Fin m)))
    (hx : x ∈ paddedLiftCarrier O hO power S U p encode) :
    Set.range p = {i | x .vf i ≠ 0} := by
  obtain ⟨t,_,lab,hz⟩ := (paddedLift_test O hO power S U p encode x).1 hx
  ext i
  constructor
  · rintro ⟨j,rfl⟩ z
    exact U.nonzero t j ((lab j).symm.trans ((rv_eq_zero_iff O).2 z))
  · intro nonzero
    by_contra h
    exact nonzero (hz i h)

omit [TopologicalSpace K] in
private theorem injective_preparation_piece
    {n i m : ℕ}
    {A : Set (SortedAssignment (CanonicalSort O) (MixedVariables n (Fin i)))}
    (defA : SortedDefinableOver 𝓜 S.carrier A)
    {B : Set (SortedAssignment (CanonicalSort O) (MixedVariables n (Fin m)))}
    (defB : SortedDefinableOver 𝓜 S.carrier B)
    (f : SortedAssignment (CanonicalSort O) (MixedVariables n (Fin i)) →
        SortedAssignment (CanonicalSort O) (MixedVariables n (Fin m)))
    (inj : Set.InjOn f A)
    (graph : DefinableRelation 𝓜 S.carrier (fun a b => f a = b))
    (range : B ⊆ f '' A) :
    let D := A ∩ f ⁻¹' B
    SortedDefinableOver 𝓜 S.carrier D ∧ MixedDefinablyEquivalent 𝓜 S D B := by
  intro D
  have hD : SortedDefinableOver 𝓜 S.carrier D := by
    have he := graph.preimage defB
    convert defA.inter he using 1
    ext a
    exact and_congr_right fun _ =>
      ⟨fun h => ⟨f a,h,rfl⟩,fun ⟨b,hb,eq⟩ => (show f a ∈ B from eq.symm ▸ hb)⟩
  let g (x : D) : B := ⟨f x.val,x.property.2⟩
  have bij : Function.Bijective g := by
    constructor
    · intro x y he
      exact Subtype.ext (inj x.property.1 y.property.1 (congrArg Subtype.val he))
    · intro y
      obtain ⟨a,ha,he⟩ := range y.property
      have hb : f a ∈ B := he.symm ▸ y.property
      exact ⟨⟨a,ha,hb⟩,Subtype.ext he⟩
  exact ⟨hD,Equiv.ofBijective g bij,(graph.inter_left hD).congr
    (fun _ _ => ⟨fun ⟨he,ha⟩ => ⟨ha,he⟩,fun ⟨ha,he⟩ => ⟨he,ha⟩⟩)⟩

/-- Every filtered VF object is a finite sum of lifts over the fixed
base, under the preparation hypotheses of Theorem 5.5. -/
theorem fieldClass_eq_sum_lifts
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ n (I : Type), Finite I →
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n I))
        (BaseAssignments S.carrier (VerticalPairVariables n I)))
    (immediate : ∀ n (b : Fin n → K) (x y : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S b)
      (∀ c : B.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t)
    (A : VFObject 𝓜 S) :
    ∃ U : Set (Fin A.2.vfArity) → GradedObject 𝓜 S, fieldClass 𝓜 S A = ∑ i, liftObjectClass (U i) := by
  classical
  let n := A.2.vfArity
  let I := Fin A.2.rvArity
  let dom := mixedTuple '' A.2.carrier
  have hd : SortedDefinableOver 𝓜 S.carrier
      {x : SortedAssignment (CanonicalSort O) (MixedVariables n I) | mixedTuple x ∈ dom} := by
    convert A.2.definable using 1
    ext a
    exact ⟨fun ⟨b,hb,he⟩ => (mixedTuple_injective he) ▸ hb,fun h => ⟨a,h,rfl⟩⟩
  obtain ⟨m,T,defT,injT,_,degree,selected,U,encode,im⟩ :=
    mixed_set_is_graded_lift O hO power S minusOne hm F hF sat immediate dom hd A.2.finiteFibers
  let W := MixedVariables n (Fin m)
  let decode := (Equiv.ofBijective mixedTuple ⟨mixedTuple_injective,mixedTuple_surjective⟩ :
    SortedAssignment (CanonicalSort O) W ≃ PreparationPoint O (Fin n) (Fin m)).symm
  let f (a : SortedAssignment (CanonicalSort O) (MixedVariables n I)) := decode (T (mixedTuple a))
  have applyF (a) : mixedTuple (f a) = T (mixedTuple a) := decode.symm_apply_apply _
  have hgraph : DefinableRelation 𝓜 S.carrier (fun a b => f a = b) := by
    unfold PointMapDefinable at defT
    apply defT.congr
    intro x y
    rw [← applyF x]
    exact ⟨fun h => mixedTuple_injective h,congrArg mixedTuple⟩
  have injF : Set.InjOn f A.2.carrier := by
    intro a ha b hb equal
    apply mixedTuple_injective
    apply injT ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact decode.injective equal
  let p (s : Set (Fin n)) : Fin (degree s) ↪ Fin n :=
    (selected s).toEmbedding.trans (Function.Embedding.subtype _)
  have rangeP (s : Set (Fin n)) : Set.range (p s) = s := by
    ext i
    exact ⟨fun ⟨j,h⟩ => h ▸ (selected s j).property,fun h =>
      ⟨(selected s).symm ⟨i,h⟩,congrArg Subtype.val ((selected s).apply_symm_apply ⟨i,h⟩)⟩⟩
  let B (s : Set (Fin n)) := paddedLiftCarrier O hO power S (U s) (p s) (encode s)
  let D (s : Set (Fin n)) := A.2.carrier ∩ f ⁻¹' B s
  have memImage (x : SortedAssignment (CanonicalSort O) W) :
      x ∈ f '' A.2.carrier ↔ ∃ s, x ∈ B s := by
    have raw : x ∈ f '' A.2.carrier ↔ mixedTuple x ∈ T '' dom := by
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ⟨mixedTuple a,⟨a,ha,rfl⟩,(applyF a).symm⟩
      · rintro ⟨_,⟨a,ha,rfl⟩,he⟩
        exact ⟨a,ha,mixedTuple_injective ((applyF a).trans he)⟩
    rw [raw,im]
    constructor
    · rintro ⟨s,t,ht,hl,hz⟩
      refine ⟨s,(paddedLift_test O hO power S (U s) (p s) (encode s) x).2 ⟨t,ht,hl,?_⟩⟩
      intro i hi
      exact hz i (rangeP s ▸ hi)
    · rintro ⟨s,h⟩
      obtain ⟨t,ht,hl,hz⟩ := (paddedLift_test O hO power S (U s) (p s) (encode s) x).1 h
      exact ⟨s,t,ht,hl,fun i hi => hz i ((rangeP s).symm ▸ hi)⟩
  have pieces (s : Set (Fin n)) : SortedDefinableOver 𝓜 S.carrier (D s) ∧
      MixedDefinablyEquivalent 𝓜 S (D s) (ObjectLift.carrier (U s)) := by
    obtain ⟨defD,iso⟩ := injective_preparation_piece O hO power S A.2.definable
      (paddedLiftCarrier_definable O hO power S (U s) (p s) (encode s)) f injF hgraph
      (fun x hx => (memImage x).2 ⟨s,hx⟩)
    exact ⟨defD,iso.trans (paddedLift_iso O hO power S (U s) (p s) (encode s))⟩
  have disj : Pairwise (fun s t => Disjoint (D s) (D t)) := by
    intro s t ne
    apply Set.disjoint_left.2
    intro x hx hy
    have hs := paddedLift_support O hO power S (U s) (p s) (encode s) (f x) hx.2
    have ht := paddedLift_support O hO power S (U t) (p t) (encode t) (f x) hy.2
    exact ne ((rangeP s).symm.trans (hs.trans (ht.symm.trans (rangeP t))))
  have cover : (⋃ s, D s) = A.2.carrier := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun _ _ h => h.1
    · intro x hx
      obtain ⟨s,hs⟩ := (memImage (f x)).1 ⟨x,hx,rfl⟩
      exact Set.mem_iUnion.2 ⟨s,hx,hs⟩
  have sub (s : Set (Fin n)) : D s ⊆ A.2.carrier := fun _ h => h.1
  refine ⟨fun s => ⟨degree s,U s⟩,(fieldClass_partition A D (fun s => (pieces s).1) sub disj cover).trans ?_⟩
  exact Finset.sum_congr rfl fun s _ => fieldClass_of_iso 𝓜 S
    (A := restrictedFieldObject A (D s) (sub s) (pieces s).1)
    (B := ⟨degree s,liftFieldObject (U s)⟩) (pieces s).2

/-- The lift is surjective on the filtered VF scissor semiring, once
every mixed set has the fixed-base preparation of Theorem 5.5. -/
theorem liftClassHom_surjective
    (liftIso : LiftsRVIsomorphisms 𝓜 S)
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L))
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (sat : ∀ n (I : Type), Finite I →
      RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (VerticalPairVariables n I))
        (BaseAssignments S.carrier (VerticalPairVariables n I)))
    (immediate : ∀ n (b : Fin n → K) (x y : K),
      let B := SortedStructure.termGenerated 𝓜 (centerAssignment O hO power S b)
      (∀ c : B.carrier .vf, rv O (x - c.val) = rv O (y - c.val)) →
      ∃ e : SortedIsomorphism 𝓜 𝓜, e.toEmbedding .vf x = y ∧
        (∀ c ∈ B.carrier .vf, e.toEmbedding .vf c = c) ∧ ∀ t, e.toEmbedding .rv t = t) :
    Function.Surjective (liftClassHom liftIso) := by
  classical
  let f := liftClassHom liftIso
  have generator (A : VFObject 𝓜 S) : ∃ x, f x = fieldClass 𝓜 S A := by
    obtain ⟨U,eq⟩ := fieldClass_eq_sum_lifts O hO power S minusOne hm F hF sat immediate A
    refine ⟨∑ i, objectClass 𝓜 S (U i),?_⟩
    rw [map_sum,eq]
    exact Finset.sum_congr rfl fun i _ => liftClassHom_class liftIso (U i)
  intro y
  let q := (ringConGen (VFRelation 𝓜 S)).mk'
  obtain ⟨p,rfl⟩ := (ringConGen (VFRelation 𝓜 S)).mk'_surjective y
  change ∃ x, f x = q p
  induction p using MvPolynomial.induction_on with
  | C n =>
    refine ⟨n,?_⟩
    rw [show MvPolynomial.C n = (n : VFExpression 𝓜 S) from map_natCast _ n,map_natCast,map_natCast]
  | add a b ha hb =>
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    exact ⟨x+y,by rw [map_add,map_add,hx,hy]⟩
  | mul_X p A hp =>
    obtain ⟨x,hx⟩ := hp
    obtain ⟨a,ha⟩ := generator A
    exact ⟨x*a,by rw [map_mul,map_mul,hx,ha]; rfl⟩

end GeneralizedEuler.Section5
