module

public import Section5.DefinableProjectedScaling
public import Section5.FiniteLabelLifting
public import Section5.PairedProjectionPartitions
public import Section5.ProjectionPartitions
public import Section5.ZeroDimensionalLabels

/-! The induction on RV dimension in all ambient arities (Lemma 5.12). -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 FirstOrder FirstOrder.Language

universe z

private theorem nat_bound_of_withBot_lt {a : WithBot ℕ} {d : ℕ}
    (hd : 0 < d) (ha : a < (d : WithBot ℕ)) :
    ∃ m : ℕ, m < d ∧ a ≤ (m : WithBot ℕ) := by
  cases a using WithBot.recBotCoe with
  | bot => exact ⟨0,hd,bot_le⟩
  | coe r => exact ⟨r,WithBot.coe_lt_coe.mp ha,le_rfl⟩

private theorem inverse_label_graph {L : Language} {E : Type*} {X : TCsort → Type z}
    {M : SortedStructure L E X} {S : SortedSubstructure M} {n : ℕ}
    {U V : Set (labelAssignment n X)} (e : U ≃ V)
    (hE : DefinableRelation M S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b)) :
    DefinableRelation M S.carrier (fun b a => ∃ hb : b ∈ V, (e.symm ⟨b,hb⟩).val = a) := by
  apply hE.transpose.congr
  intro b a
  constructor
  · rintro ⟨ha,rfl⟩
    exact ⟨(e ⟨a,ha⟩).property, congrArg Subtype.val (e.symm_apply_apply ⟨a,ha⟩)⟩
  · rintro ⟨hb,rfl⟩
    exact ⟨(e.symm ⟨b,hb⟩).property, congrArg Subtype.val (e.apply_symm_apply ⟨b,hb⟩)⟩

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  [LinearOrder (RV0 O)] [DenselyOrdered (RV0 O)] [TopologicalSpace (RV0 O)] [OrderTopology (RV0 O)]

local notation "𝓜" => canonicalStructure (L := L) O hO power

/-- Fixed-base lifting in all finite arities. The RV dimension inputs
are the finite union and transport laws, the pointwise coordinate
basis bound, and the boundary estimate of Section 3. -/
theorem definable_field_lift_by_dimension
    (satVF : ∀ n, RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (MixedVariables n Empty))
      (BaseAssignments S.carrier (MixedVariables n Empty)))
    (satRV : ∀ n, RealizesFinitelySatisfiableTypes 𝓜 (WithBase S.carrier (RVVariables (Fin n)))
      (BaseAssignments S.carrier (RVVariables (Fin n))))
    (elem : ∀ n (a : fieldAssignment n (CanonicalSort O)), let C := (𝓜).termGenerated (namedFieldAssignment S a)
      ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → C.carrier s),
        φ.realize C.structureOn v ↔ φ.realize 𝓜 (fun s i => (v s i).val))
    (elemBase : ∀ {W : TCsort → Type z} (φ : SortedFormula L E W) (v : ∀ s, W s → S.carrier s),
      φ.realize S.structureOn v ↔ φ.realize 𝓜 (fun s => Subtype.val ∘ v s))
    (generated : S.structureOn.IsVFGenerated)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (tame : ∀ C : Set (RV0 O),
      SortedDefinableOver 𝓜 S.carrier {x : labelAssignment 1 (CanonicalSort O) | x .rv 0 ∈ C} →
      FiniteConvexUnion C)
    (dimUnion : ∀ n (A B : Set (labelAssignment n (CanonicalSort O))),
      SortedDefinableOver 𝓜 S.carrier A → SortedDefinableOver 𝓜 S.carrier B →
      labelProjectionDimension (A ∪ B) ≤ max (labelProjectionDimension A) (labelProjectionDimension B))
    (dimTransport : ∀ n {U V : Set (labelAssignment n (CanonicalSort O))} (e : U ≃ V),
      DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b) →
      ∀ C, SortedDefinableOver 𝓜 S.carrier C →
        labelProjectionDimension (rvPreimage e C) ≤ labelProjectionDimension C)
    (pointwiseBasis : ∀ n d, d ≤ n → ∀ A : Set (labelAssignment n (CanonicalSort O)),
      SortedDefinableOver 𝓜 S.carrier A → labelProjectionDimension A ≤ (d : WithBot ℕ) →
      ∀ x ∈ A, ∃ (p : Fin d ↪ Fin n) (B : Set (labelAssignment n (CanonicalSort O))),
        SortedDefinableOver 𝓜 S.carrier B ∧ x ∈ projectionUnique p B)
    (boundary : ∀ n (A : Set (Fin n → K)),
      BlockDefinable 𝓜 (fun s (a : S.carrier s) => a.val) .vf A →
      projectionDimensionWithBot (rvBoundary (fun a => (𝓜).rvMap ∘ a) A) < (n : WithBot ℕ)) :
    ∀ (d n : ℕ) (U V : Set (labelAssignment n (CanonicalSort O))) (e : U ≃ V),
      SortedDefinableOver 𝓜 S.carrier U → SortedDefinableOver 𝓜 S.carrier V →
      DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ U, (e ⟨a,ha⟩).val = b) →
      (∀ u ∈ U, ∀ j, u .rv j ≠ 0) → (∀ v ∈ V, ∀ j, v .rv j ≠ 0) →
      labelProjectionDimension U ≤ (d : WithBot ℕ) → HasDefinableFieldLift S e := by
  have surj : Function.Surjective (𝓜).rvMap := by
    intro t
    obtain ⟨x,hx⟩ := rv_surjective O t
    exact ⟨x,(canonicalStructure_rvMap O hO power x).trans hx⟩
  intro d
  induction d using Nat.strong_induction_on with
  | h d lower =>
    intro n U V e hU hV hE nzU nzV dimU
    rcases Nat.eq_zero_or_pos d with hZero | hPos
    · subst d
      have finiteU := finite_of_labelProjectionDimension_le_zero tame hU (by simpa using dimU)
      exact definable_finite_label_lift_of_elementary O hO power S e finiteU hU hV nzU nzV
        elemBase generated F minusOne hm hF
    have full : ∀ (D G : Set (labelAssignment d (CanonicalSort O))) (g : D ≃ G),
        SortedDefinableOver 𝓜 S.carrier D → SortedDefinableOver 𝓜 S.carrier G →
        DefinableRelation 𝓜 S.carrier (fun a b => ∃ ha : a ∈ D, (g ⟨a,ha⟩).val = b) →
        (∀ a ∈ D, ∀ j, a .rv j ≠ 0) → (∀ b ∈ G, ∀ j, b .rv j ≠ 0) →
        HasDefinableFieldLift S g := by
      intro D G g hD hG hGraph nzD nzG
      apply definable_full_arity_lift_from_boundary (satVF d) (elem d) g hD hG hGraph surj
        labelProjectionDimension (d : WithBot ℕ) labelProjectionDimension_mono (dimUnion d)
        (dimTransport d g hGraph) (fieldLead_boundary_dimension_lt (boundary d))
      intro A hA hSmall
      obtain ⟨m,hm',dimA⟩ := nat_bound_of_withBot_lt hPos hSmall
      have hTarget := restrictedLabelEquiv_target_definable g A hA hGraph
      have nzA : ∀ a ∈ (Subtype.val '' A : Set (labelAssignment d (CanonicalSort O))),
          ∀ j, a .rv j ≠ 0 := by
        rintro _ ⟨a,_,rfl⟩
        exact nzD _ a.property
      have nzG' : ∀ b ∈ (Subtype.val '' (g '' A) : Set (labelAssignment d (CanonicalSort O))),
          ∀ j, b .rv j ≠ 0 := by
        rintro _ ⟨b,_,rfl⟩
        exact nzG _ b.property
      exact relative_lift_of_restricted g A
        (lower m hm' d _ _ _ hA hTarget (restrictedLabelEquiv_graph g A hA hGraph) nzA nzG' dimA)
    rcases lt_trichotomy n d with hn | rfl | hn
    · exact lower n hn n U V e hU hV hE nzU nzV (labelProjectionDimension_le_arity U)
    · exact full U V e hU hV hE nzU nzV
    have eqV : rvPreimage e.symm U = V := by
      ext v
      exact ⟨fun ⟨hv,_⟩ => hv, fun hv => ⟨hv,(e.symm ⟨v,hv⟩).property⟩⟩
    have dimV : labelProjectionDimension V ≤ (d : WithBot ℕ) := by
      rw [← eqV]
      exact (dimTransport n e.symm (inverse_label_graph e hE) U hU).trans dimU
    obtain ⟨N,P,p,hP,disjP,coverP,injP⟩ := definable_injective_projection_partition (satRV n) U hU
      (pointwiseBasis n d hn.le U hU dimU)
    obtain ⟨J,Q,q,hQ,disjQ,coverQ,injQ⟩ := definable_injective_projection_partition (satRV n) V hV
      (pointwiseBasis n d hn.le V hV dimV)
    apply definable_lift_of_paired_projections e hE P Q hP hQ p q injP injQ disjP disjQ coverP coverQ
    intro A hA p' q' injA injB
    let B := Subtype.val '' (e '' A)
    let g := restrictedLabelEquiv e A
    have hB := restrictedLabelEquiv_target_definable e A hA hE
    have gDef := restrictedLabelEquiv_graph e A hA hE
    have nzA : ∀ a ∈ (Subtype.val '' A : Set (labelAssignment n (CanonicalSort O))),
        ∀ i, a .rv i ≠ 0 := by
      rintro _ ⟨a,_,rfl⟩
      exact nzU _ a.property
    have nzB : ∀ b ∈ B, ∀ i, b .rv i ≠ 0 := by
      rintro _ ⟨b,_,rfl⟩
      exact nzV _ b.property
    have nzP : ∀ a ∈ projectLabels p' '' (Subtype.val '' A), ∀ j, a .rv j ≠ 0 := by
      rintro _ ⟨a,ha,rfl⟩ j
      exact nzA _ ha (p' j)
    have nzQ : ∀ b ∈ projectLabels q' '' B, ∀ j, b .rv j ≠ 0 := by
      rintro _ ⟨b,hb,rfl⟩ j
      exact nzB _ hb (q' j)
    apply definable_lift_of_injective_projection O hO power S p' q' g injA injB hA hB nzA nzB
      (satVF d) (elem d) F minusOne hm hF
    exact full _ _ _ (projectLabels_image_definable p' hA) (projectLabels_image_definable q' hB)
      (projectedLabelEquiv_definable g p' q' injA injB gDef) nzP nzQ

end GeneralizedEuler.Section5
