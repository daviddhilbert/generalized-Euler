module

public import Section5.TerminalUnaryRows
public import Section5.UnaryHeadSliceComparison
public import Section5.RVAppendLabel
import all Section4.Objects

/-! The unary kernel's label class is the class of the named terminal
rows on each retained slice. The leading term already in the history
can be read twice by a definable coordinate embedding. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder RelativeObjectFamily

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k a m : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => RVVariables (Fin k)

variable {A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 1 k}

set_option maxHeartbeats 600000 in
theorem HeadContractionData.terminalUnaryRows_class
    (H : HeadContractionData (n := 0) A)
    (tags : Fin a ≃ H.target.tags) (idx : Fin m ≃ Fin 1 ⊕ H.target.tags)
    (zero : S.carrier .rv) (hz : zero.val = 0) (b₀ b₁ : ℕ)
    (p : SortedAssignment Z P)
    (v : Valid (H.target.terminalUnaryRows tags zero b₀ b₁) zero p) :
    let T := (𝓜).termGenerated (namedTuple S p)
    letI := H.target.finiteTags
    fiberClass (H.target.terminalUnaryRows tags zero b₀ b₁) zero hz p v =
      unaryLabelClass O hO power T (H.unarySlice (p .rv)) idx (H.unarySlice_definable p)
        (H.unarySlice_pullback (p .rv)) (H.unarySlice_finite (p .rv)) := by
  intro T
  let := H.target.finiteTags
  let B := H.target
  let U := B.terminalUnaryRows tags zero b₀ b₁
  let V := unaryLabelObjects O hO power T (H.unarySlice (p .rv)) idx (H.unarySlice_definable p)
    (H.unarySlice_pullback (p .rv)) (H.unarySlice_finite (p .rv))
  let fieldTag := idx.symm (.inl 0)
  let lead := B.terminalNewLead tags
  let old := B.terminalOldHead tags
  let order : Fin m ≃ Fin a ⊕ Fin 1 :=
    idx.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr tags.symm (Equiv.refl _)))
  let cls := objectClass 𝓜 T
  have align {d : ℕ} (C D : RVObject 𝓜 T d) (c : C.arity = a) (d' : D.arity = m)
      (cut : RV0 O → Prop)
      (src : ∀ t : Fin a → RV0 O, t ∘ Fin.cast c ∈ C.carrier ↔
        t ∈ B.terminalLabels tags ∧ t ∘ old = p .rv ∧ cut (t lead))
      (dst : ∀ w : Fin m → RV0 O, w ∘ Fin.cast d' ∈ D.carrier ↔
        w ∈ reindexedUnaryLabels O (H.unarySlice (p .rv)) idx ∧ cut (w fieldTag)) :
      cls ⟨d,C⟩ = cls ⟨d,D⟩ := by
    let X₀ := {t : Fin a → RV0 O | t ∘ Fin.cast c ∈ C.carrier}
    let Y₀ := {w : Fin m → RV0 O | w ∘ Fin.cast d' ∈ D.carrier}
    have cIso := rv_cast_carrier_equiv C c X₀ (fun _ => Iff.rfl)
    have dIso := rv_cast_carrier_equiv D d' Y₀ (fun _ => Iff.rfl)
    have dX : isRVSet 𝓜 T X₀ := isRVSet_precomp (Fin.cast c) C.definable
    have coord : DefinableRelation 𝓜 T.carrier
        (fun (x : SortedAssignment Z (RVVariables (Fin a))) (y : SortedAssignment Z (RVVariables (Fin 1))) =>
          x .rv lead = y .rv 0) :=
      SortedDefinableOver.coordinate_eq (M := 𝓜) (A := T.carrier)
        (Var := SumVariables (RVVariables (Fin a)) (RVVariables (Fin 1))) .rv (.inl lead) (.inr 0)
    let G := {x : Fin a ⊕ Fin 1 → RV0 O | x ∘ Sum.inl ∈ X₀ ∧ x (.inr 0) = x (.inl lead)}
    have gIso : RVDefinablyEquivalent 𝓜 T.carrier X₀ G := rv_equiv_append_label X₀ dX (fun t => t lead) coord
    have dG := isRVSet_of_rvEquiv (M := 𝓜) (S := T) gIso
    have pack := rv_reindex_equivalent 𝓜 T order G dG
    have same : {w | w ∘ order.symm ∈ G} = Y₀ := by
      ext w
      let x : Fin a → RV0 O := w ∘ order.symm ∘ Sum.inl
      let t : H.target.tags → RV0 O := w ∘ idx.symm ∘ Sum.inr
      have extra : w (order.symm (.inr 0)) = w fieldTag := by simp [order,fieldTag]
      have tagged : x ∘ tags.symm = t := by
        funext i
        simp [x,t,order]
      have oldHead : x ∘ old = t ∘ B.select ∘ Fin.castSucc := by
        change (x ∘ tags.symm) ∘ B.select ∘ Fin.castSucc = _
        rw [tagged]
      have newLead : x lead = t (B.select (Fin.last k)) := congrFun tagged _
      have source : x ∈ X₀ ↔
          (Fin.elim0,t) ∈ B.carrier ∧ t ∘ B.select ∘ Fin.castSucc = p .rv ∧ cut (t (B.select (Fin.last k))) := by
        refine (src x).trans ?_
        change ((Fin.elim0,x ∘ tags.symm) ∈ B.carrier ∧ x ∘ old = p .rv ∧ cut (x lead)) ↔ _
        rw [tagged,oldHead,newLead]
      have dest := dst w
      rw [H.unarySlice_labelSet (p .rv) idx] at dest
      change (x ∈ X₀ ∧ w (order.symm (.inr 0)) = x lead) ↔ w ∘ Fin.cast d' ∈ D.carrier
      rw [source,extra,newLead,dest]
      constructor
      · rintro ⟨⟨h,hold,hcut⟩,he⟩
        exact ⟨⟨h,hold,he⟩,he.symm ▸ hcut⟩
      · rintro ⟨⟨h,hold,he⟩,hcut⟩
        have sameLead : w fieldTag = t (B.select (Fin.last k)) := he
        exact ⟨⟨h,hold,sameLead ▸ hcut⟩,he⟩
    rw [same] at pack
    exact scissors_sound 𝓜 T (.iso C D (cIso.trans (gIso.trans (pack.trans dIso.symm))))
  have lower := align ((U 0).realize zero hz p (v 0)) V.1 rfl rfl (· = 0)
    (fun t => by
      change ((_ ∧ _) ∧ t lead = zero.val) ↔ _
      rw [hz]
      exact and_assoc)
    (fun _ => Iff.rfl)
  have upper := align ((U 1).realize zero hz p (v 1)) V.2 rfl rfl (· ≠ 0)
    (fun t => by
      change ((_ ∧ _) ∧ t lead ≠ zero.val) ↔ _
      rw [hz]
      exact and_assoc)
    (fun _ => Iff.rfl)
  change (∑ i : Fin 2, cls ⟨(U i).data.degree,(U i).realize zero hz p (v i)⟩) = cls ⟨0,V.1⟩ + cls ⟨1,V.2⟩
  rw [Fin.sum_univ_two]
  exact congrArg₂ (· + ·) lower upper

end GeneralizedEuler.Section5
