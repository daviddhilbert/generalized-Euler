module

public import Section5.UnaryTranslationPullback
public import Section5.TranslatedDiscMaps
import all Section5.PairedSourceTranslation

/-! A paired unary step gives actual translated pullbacks and the
contraction of their conjugated bijection. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {R T : Type*} {A : Set (K × R)} {B : Set (K × T)}

/-- A disc-to-disc chart on the old source fiber, including both tags
through the agreement condition on the original map. -/
@[expose] def UnaryDiscCharts (e : A ≃ B) : Prop :=
  ∀ x : A, x.val.1 ≠ 0 →
    ∃ (b : K) (r : O.ValueGroup) (f₀ g₀ : K → K),
      r ≠ 0 ∧ DiscToDiscOn O (openDisc O x.val.1 (O.valuation x.val.1)) (openDisc O b r) f₀ g₀ ∧
        (∀ a : A, unaryMixedLabel O a.val = unaryMixedLabel O x.val → f₀ a.val.1 = (e a).val.1) ∧
        (∀ u ∈ openDisc O x.val.1 (O.valuation x.val.1), ∃ a : A,
          a.val.1 = u ∧ unaryMixedLabel O a.val = unaryMixedLabel O x.val)

@[expose] def unaryImageIso {I : Type*} (D : Set (K × I))
    (S : RelativeTranslation O (id : I → I)) : D ≃ recodeUnaryTranslation O S '' D :=
  Equiv.Set.image (recodeUnaryTranslation O S) D (recodeUnaryTranslation_injective O S)

variable (e : A ≃ B) (C : Set (RV0 O × T)) (focus : RV0 O × T → B)

local notation "S" => pairedSourceTranslation O e C focus
local notation "T₁" => pairedTargetTranslation O C focus

@[expose] def pairedUnaryConjugate :
    (recodeUnaryTranslation O S '' A) ≃ (recodeUnaryTranslation O T₁ '' B) :=
  (unaryImageIso O A S).symm.trans (e.trans (unaryImageIso O B T₁))

theorem pairedUnaryConjugate_apply (x : A) :
    (pairedUnaryConjugate O e C focus (unaryImageIso O A S x)).val =
      recodeUnaryTranslation O T₁ (e x).val := by
  change (unaryImageIso O B T₁ (e ((unaryImageIso O A S).symm (unaryImageIso O A S x)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem paired_unary_step_preserves_pullbacks
    (hA : IsUnaryPullback O A) (hB : IsUnaryPullback O B)
    (focusLabel : ∀ t ∈ C, unaryMixedLabel O (focus t).val = t) :
    IsUnaryPullback O (recodeUnaryTranslation O S '' A) ∧
      IsUnaryPullback O (recodeUnaryTranslation O T₁ '' B) := by
  refine ⟨recodeUnaryTranslation_preserves_pullback O S A hA
    (fun _ _ h => pairedSourceTranslation_focus_lead O e C focus h),
    recodeUnaryTranslation_preserves_pullback O T₁ B hB ?_⟩
  intro r t h
  exact congrArg (fun p : RV0 O × T => p.1) (focusLabel (t,r) h)

theorem paired_unary_step_contracts
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e)
    (chart : UnaryDiscCharts O e)
    (focusLabel : ∀ t ∈ C, unaryMixedLabel O (focus t).val = t) :
    Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) (pairedUnaryConjugate O e C focus) := by
  intro x y same
  obtain ⟨x,rfl⟩ := (unaryImageIso O A S).surjective x
  obtain ⟨y,rfl⟩ := (unaryImageIso O A S).surjective y
  have old : unaryMixedLabel O x.val = unaryMixedLabel O y.val := by
    have raw := congrArg (fun t : RV0 O × (R × RV0 O) => (t.2.2,t.2.1)) same
    exact raw
  have current : mixedSourceFocusLabel O e C focus x = mixedSourceFocusLabel O e C focus y := by
    have h := congrArg (fun t : RV0 O × (R × RV0 O) => t.1) same
    change rv O ((S).map (x.val.2,x.val.1)).2.1 = rv O ((S).map (y.val.2,y.val.1)).2.1 at h
    rw [pairedSourceTranslation_label O e C focus contract x,pairedSourceTranslation_label O e C focus contract y] at h
    exact h
  have new := (paired_mixed_focus_matches_labels O e contract C focus focusLabel old (chart x)).1 current
  have prev := contract x y old
  change unaryMixedLabel O (pairedUnaryConjugate O e C focus (unaryImageIso O A S x)).val =
    unaryMixedLabel O (pairedUnaryConjugate O e C focus (unaryImageIso O A S y)).val
  rw [pairedUnaryConjugate_apply O e C focus x,pairedUnaryConjugate_apply O e C focus y]
  apply Prod.ext
  · change rv O ((T₁).map ((e x).val.2,(e x).val.1)).2.1 =
      rv O ((T₁).map ((e y).val.2,(e y).val.1)).2.1
    rw [pairedTargetTranslation_label O C focus (e x),pairedTargetTranslation_label O C focus (e y)]
    exact new
  · exact congrArg (fun t : RV0 O × T => (t.2,t.1)) prev

/-- The inverse of the conjugated map refines the source label when
the final target label already refines the old source and the current
target labels. -/
theorem paired_unary_step_inverse_contracts {P : Type*}
    (contract : Contractible (unaryMixedLabel O ∘ Subtype.val)
      (unaryMixedLabel O ∘ Subtype.val) e)
    (chart : UnaryDiscCharts O e)
    (focusLabel : ∀ t ∈ C, unaryMixedLabel O (focus t).val = t)
    (final : (recodeUnaryTranslation O T₁ '' B) → P)
    (oldInverse : Contractible (final ∘ unaryImageIso O B T₁)
      (unaryMixedLabel O ∘ Subtype.val) e.symm)
    (targetRefines : ∀ y z, final y = final z → unaryMixedLabel O y.val = unaryMixedLabel O z.val) :
    Contractible final (unaryMixedLabel O ∘ Subtype.val) (pairedUnaryConjugate O e C focus).symm := by
  intro y z eq
  obtain ⟨y,rfl⟩ := (unaryImageIso O B T₁).surjective y
  obtain ⟨z,rfl⟩ := (unaryImageIso O B T₁).surjective z
  have old := oldInverse y z eq
  have tgt := targetRefines _ _ eq
  have current : mixedTargetFocusLabel O C focus y = mixedTargetFocusLabel O C focus z := by
    have h := congrArg (fun t : RV0 O × (T × RV0 O) => t.1) tgt
    change rv O ((T₁).map (y.val.2,y.val.1)).2.1 = rv O ((T₁).map (z.val.2,z.val.1)).2.1 at h
    rw [pairedTargetTranslation_label O C focus y,pairedTargetTranslation_label O C focus z] at h
    exact h
  have hSrc := (paired_mixed_focus_matches_labels O e contract C focus focusLabel old (chart (e.symm y))).2
    (by simpa only [Equiv.apply_symm_apply] using current)
  change unaryMixedLabel O
      ((unaryImageIso O A S) (e.symm ((unaryImageIso O B T₁).symm ((unaryImageIso O B T₁) y)))).val =
    unaryMixedLabel O
      ((unaryImageIso O A S) (e.symm ((unaryImageIso O B T₁).symm ((unaryImageIso O B T₁) z)))).val
  simp only [Equiv.symm_apply_apply]
  apply Prod.ext
  · change rv O ((S).map ((e.symm y).val.2,(e.symm y).val.1)).2.1 =
      rv O ((S).map ((e.symm z).val.2,(e.symm z).val.1)).2.1
    rw [pairedSourceTranslation_label O e C focus contract (e.symm y),
      pairedSourceTranslation_label O e C focus contract (e.symm z)]
    exact hSrc
  · exact congrArg (fun t : RV0 O × R => (t.2,t.1)) old

end GeneralizedEuler.Section5
