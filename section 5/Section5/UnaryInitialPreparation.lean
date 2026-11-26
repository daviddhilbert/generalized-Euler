module

public import Section5.UnaryChainFibers

/-! Prepare any finite list of definable tests on a unary pullback.
Identity charts let the paired construction supply the single chain. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] (O : ValuationSubring K) {R : Type*} {A : Set (K × R)}

theorem unary_identity_disc_charts (full : IsUnaryPullback O A) : UnaryDiscCharts O (Equiv.refl A) := by
  intro x nz
  let D := openDisc O x.val.1 (O.valuation x.val.1)
  have rd : O.valuation x.val.1 ≠ 0 := (map_ne_zero _).2 nz
  have dtd : DiscToDiscOn O D D id id := by
    refine ⟨⟨fun _ h => h,fun _ _ _ _ eq => eq,?_⟩,
      ⟨fun _ _ => rfl,fun _ _ => rfl⟩,?_,?_⟩
    · intro u hu
      exact ⟨u,hu,rfl⟩
    · exact fun c r hr _ => ⟨c,r,hr,Set.image_id _⟩
    · exact fun c r hr _ => ⟨c,r,hr,Set.image_id _⟩
  refine ⟨x.val.1,O.valuation x.val.1,id,id,rd,dtd,fun _ _ => rfl,?_⟩
  intro u hu
  have label : unaryMixedLabel O (u,x.val.2) = unaryMixedLabel O x.val :=
    Prod.ext ((rv_eq_rv_iff_valuation O nz).2 hu) rfl
  exact ⟨⟨(u,x.val.2),full x.val x.property _ label.symm⟩,rfl,label⟩

variable [LinearOrder K] [IsStrictOrderedRing K] {L : Language} [L.Structure K]
  {E : Type*} [L.Structure (Residue O)] (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {I : Type} [Finite I]

theorem definable_center_preparation_on_pullback
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (B : Set (K × (I → RV0 O))) (defB : UnaryPullbackDefinable O hO power S B)
    (full : IsUnaryPullback O B) (centers : List (CenterTest O I))
    (defC : ∀ c ∈ centers, CenterTestDefinable O hO power S c) :
    ∃ (I' : Type) (_ : Finite I') (B' : Set (K × (I' → RV0 O))) (t : B ≃ B'),
      EncodedFocusChain O (fun _ T => UnaryOffsetDefinable O hO power S T) B B' t ∧
      UnaryMixedGraphDefinable O hO power S t ∧ IsUnaryPullback O B' ∧
      ∀ x y : B, unaryMixedLabel O (t x).val = unaryMixedLabel O (t y).val →
        ∀ c ∈ centers, centerTestValue O c x.val = centerTestValue O c y.val := by
  obtain ⟨_,I',_,fi,_,B',_,t,_,ht,_,hg,_,hb,_,_,tests⟩ :=
    definable_paired_center_chains O hO power S F minusOne hm hF (Equiv.refl B) defB defB
      (unaryMixedGraph_refl O hO power S B defB) full full (unary_identity_disc_charts O full)
      (fun _ _ h => h) centers defC (fun _ _ h _ => h)
  exact ⟨I',fi,B',t,ht,hg,hb,tests⟩

end GeneralizedEuler.Section5
