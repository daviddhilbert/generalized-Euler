module

public import Section5.PairedUnaryGraphs

/-! The paired conjugation is a composition of the two translation
graphs and the original graph, all over the same base. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {I J : Type} [Finite I] [Finite J]

local notation "𝓜" => canonicalStructure (L := L) O hO power

@[expose] def extendedUnaryPair {H : Type}
    (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 (H ⊕ Unit))) :
    K × ((H → RV0 O) × RV0 O) :=
  (a .vf 0,(a .rv ∘ Sum.inl,a .rv (.inr ())))

theorem recodeUnaryTranslation_graph_definable
    (T : RelativeTranslation O (id : (I → RV0 O) → (I → RV0 O)))
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (defOffset : DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I))
        (v : fieldAssignment 1 (CanonicalSort O)) => v .vf 0 = T.offset (a .rv) (rv O (a .vf 0)))) :
    DefinableRelation 𝓜 S.carrier
      (fun a b => recodeUnaryTranslation O T (unaryPair O a) = extendedUnaryPair O b) := by
  let offset (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 I)) :=
    T.offset (a .rv) (rv O (a .vf 0))
  have graph := unary_translation_graph_definable O hO power S F minusOne hm hF
    (fun a c => c = offset a) defOffset
  refine graph.congr ?_
  intro a b
  constructor
  · rintro ⟨c,rfl,hf,htags,hLead⟩
    exact Prod.ext hf.symm (Prod.ext (funext fun i => (htags i).symm) hLead.symm)
  · intro eq
    refine ⟨offset a,rfl,(congrArg Prod.fst eq).symm,?_,?_⟩
    · exact fun i => (congrFun (congrArg (Prod.fst ∘ Prod.snd) eq) i).symm
    · exact (congrArg (Prod.snd ∘ Prod.snd) eq).symm

variable {A : Set (K × (I → RV0 O))} {B : Set (K × (J → RV0 O))}
  (e : A ≃ B) (C : Set (RV0 O × (J → RV0 O))) (focus : RV0 O × (J → RV0 O) → B)

local notation "T₁" => pairedSourceTranslation O e C focus
local notation "T₂" => pairedTargetTranslation O C focus

theorem pairedUnaryConjugate_definable
    (eDef : UnaryMixedGraphDefinable O hO power S e)
    (cDef : targetFocusGraphDefinable O hO power S C focus)
    (full : IsUnaryPullback O A)
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) :
    DefinableRelation 𝓜 S.carrier
      (fun (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 (I ⊕ Unit)))
        (b : SortedAssignment (CanonicalSort O) (MixedVariables 1 (J ⊕ Unit))) =>
        ∃ ha : extendedUnaryPair O a ∈ recodeUnaryTranslation O T₁ '' A,
          (pairedUnaryConjugate O e C focus ⟨extendedUnaryPair O a,ha⟩).val = extendedUnaryPair O b) := by
  have first := recodeUnaryTranslation_graph_definable O hO power S T₁ F minusOne hm hF
    (pairedSourceOffset_definable O hO power S e C focus eDef cDef full contract)
  have second := recodeUnaryTranslation_graph_definable O hO power S T₂ F minusOne hm hF
    (pairedTargetOffset_definable O hO power S C focus cDef)
  refine ((first.transpose.comp eDef).comp second).congr ?_
  intro a b
  constructor
  · rintro ⟨y,⟨x,hx,ha,he⟩,hb⟩
    let p : A := ⟨unaryPair O x,ha⟩
    have img : (unaryImageIso O A T₁ p).val = extendedUnaryPair O a := hx
    have mem : extendedUnaryPair O a ∈ recodeUnaryTranslation O T₁ '' A :=
      img ▸ (unaryImageIso O A T₁ p).property
    refine ⟨mem,?_⟩
    have pt : (⟨extendedUnaryPair O a,mem⟩ : (recodeUnaryTranslation O T₁ '' A)) = unaryImageIso O A T₁ p :=
      Subtype.ext img.symm
    rw [pt,pairedUnaryConjugate_apply O e C focus p]
    change (e p).val = unaryPair O y at he
    rw [he]
    exact hb
  · rintro ⟨ha,hb⟩
    obtain ⟨p,hp⟩ := (unaryImageIso O A T₁).surjective ⟨extendedUnaryPair O a,ha⟩
    let pack {H : Type} (w : K × (H → RV0 O)) :
        SortedAssignment (CanonicalSort O) (MixedVariables 1 H)
      | .vf => fun _ => w.1
      | .rv => w.2
    refine ⟨pack (e p).val,⟨pack p.val,congrArg Subtype.val hp,p.property,rfl⟩,?_⟩
    rw [← hp,pairedUnaryConjugate_apply O e C focus p] at hb
    exact hb

end GeneralizedEuler.Section5
