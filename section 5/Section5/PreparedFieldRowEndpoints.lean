module

public import Section5.FieldRVFiberRows
public import Section5.HeadContractionFromCenters
public import Section5.GluedRowClassRealization
public import Section5.PreparedUnaryRVIndex

/-! When the common unary preparation contracts a named field family,
each descended RV row glues to the actual terminal object on the
combined old and new zero pattern. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder FirstOrder.Language

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power)) {k a h : ℕ}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O
local notation "P" => MixedVariables 1 Empty

variable (A : RetainedFieldFamily (canonicalStructure (L := L) O hO power) S 1 k)
  (idx : Fin a ≃ A.tags) (cs : List (S.carrier .vf)) (e : Fin h ≃ HistoryIndex cs.length)

local notation "T" => UnaryPreparation.prepare (UnaryPreparation.regularize (O := O)) Subtype.val cs

@[expose] def preparedHeadTagOrder : Fin (h+a) ≃ HistoryIndex cs.length ⊕ A.tags :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr e idx)

set_option maxHeartbeats 900000 in
theorem prepared_field_row_gluedClass
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (D : Set (SortedAssignment Z P)) (defD : SortedDefinableOver 𝓜 S.carrier D)
    (contains : ∀ p u, appendAssignments p u ∈ A.fieldFiberTags idx → p ∈ D)
    (same : ∀ x y (t : A.tags → RV0 O), (T).label x = (T).label y →
      (((fun _ => x),t) ∈ A.carrier ↔ ((fun _ => y),t) ∈ A.carrier))
    (zero : S.carrier .rv) (hz : zero.val = 0)
    (s : Finset (Fin k)) (new : Bool) (bound : ℕ)
    (I : RelativeRVIndex (X := CanonicalSort O) 𝓜 S h new.toNat)
    (index : I.labels = {q ∈ preparedHistoryLabels O hO power S cs e D |
      q (e.symm (lastIndex cs.length)) ≠ 0 ↔ new = true}) :
    let H := HeadContractionData.ofUnaryCenters O hO power S A cs minusOne hm F hF same
    let defH := preparedHistoryRelation_definable O hO power S cs e F minusOne hm hF defD
    let W := (A.fieldFiberRow idx zero s bound).descend defH
    ∀ (v : ∀ q ∈ I.labels, W.valid zero (rvTupleAssignment q)),
      (W.row zero hz I v).gluedClass =
        objectClass 𝓜 S (H.target.terminalGradedPiece (preparedHeadTagOrder O hO power S A idx cs e)
          (extendTerminalSupport s new) zero hz) := by
  intro H defH W v
  let order := preparedHeadTagOrder O hO power S A idx cs e
  let keep := RetainedFieldFamily.supportEnumeration s
  let X₀ := H.target.terminalPiece order (terminalUnaryKeep keep new) zero hz
  have sameClass := H.target.terminalUnaryPiece_class_eq_support order zero hz s new
  refine Eq.trans ?_ sameClass
  apply (W.row zero hz I v).gluedClass_realized X₀ (Nat.add_comm _ _) rfl
  intro x
  change (Fin (h+a) → RV0 O) at x
  let q : Fin h → RV0 O := x ∘ rvHead
  let r : Fin a → RV0 O := x ∘ rvTail
  let tags := x ∘ order.symm
  have head : tags ∘ Sum.inl = q ∘ e.symm := by
    funext i
    simp [tags,order,preparedHeadTagOrder,q,rvHead,Function.comp_apply]
  have tail : tags ∘ Sum.inr = r ∘ idx.symm := by
    funext i
    simp [tags,order,preparedHeadTagOrder,r,rvTail,Function.comp_apply]
  have old (i : Fin k) : x (H.target.terminalOldHead order i) = r (idx.symm (A.select i)) := by
    have sel : H.target.select (Fin.castSucc i) = Sum.inr (A.select i) := by
      simp only [HeadContractionData.target,Fin.lastCases_castSucc,Function.comp_apply]
    change tags (H.target.select (Fin.castSucc i)) = _
    rw [sel]
    exact congrFun tail (A.select i)
  have lead : x (H.target.terminalNewLead order) = q (e.symm (lastIndex cs.length)) := by
    have sel : H.target.select (Fin.last k) = Sum.inl (lastIndex cs.length) := by
      simp only [HeadContractionData.target,Fin.lastCases_last,H,HeadContractionData.ofUnaryCenters]
    change tags (H.target.select (Fin.last k)) = _
    rw [sel]
    exact congrFun head (lastIndex cs.length)
  have left (x₁ : K) : Fin.cons x₁ (Fin.elim0 : Fin 0 → K) = fun _ => x₁ := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  have terminal : x ∈ H.target.terminalLabels order ↔
      ∃ x₁, (((fun _ => x₁),r ∘ idx.symm) ∈ A.carrier) ∧ (T).label x₁ = decodeHistory O cs.length (q ∘ e.symm) := by
    change (∃ x₁, (Fin.cons x₁ Fin.elim0,tags ∘ Sum.inr) ∈ A.carrier ∧
      (T).label x₁ = decodeHistory O cs.length (tags ∘ Sum.inl)) ↔ _
    simp only [head,tail,left]
  have leftMembership : x ∈ X₀.carrier ↔
      x ∈ H.target.terminalLabels order ∧
      (∀ i, r (idx.symm (A.select i)) ≠ zero.val ↔ i ∈ s) ∧
      (q (e.symm (lastIndex cs.length)) ≠ 0 ↔ new = true) := by
    have shape := H.target.terminalUnaryPiece_mem order keep zero hz new x
    refine shape.trans (and_congr_right fun _ => and_congr ?_ ?_)
    · refine forall_congr' (fun i => iff_congr ?_ ?_)
      · exact not_congr (congrArg (· = zero.val) (old i)).to_iff
      · rw [show Set.range keep = (s : Set (Fin k)) from RetainedFieldFamily.range_supportEnumeration s]
        rfl
    · exact iff_congr (not_congr (congrArg₂ (· = ·) lead hz).to_iff) Iff.rfl
  change x ∈ X₀.carrier ↔ q ∈ I.labels ∧
    appendAssignments (rvTupleAssignment q) (rvTupleAssignment r) ∈ descendFiberScheme
      (preparedHistoryRelation O hO power S cs e D) (A.fieldFiberSupportTags idx zero s)
  rw [leftMembership,terminal,index]
  constructor
  · rintro ⟨⟨x₁,hx,hh⟩,support,hn⟩
    let p : SortedAssignment Z P := fieldTupleAssignment (fun _ => x₁)
    have mem : appendAssignments p (rvTupleAssignment r) ∈ A.fieldFiberTags idx := hx
    have dom := contains p (rvTupleAssignment r) mem
    have relation : preparedHistoryRelation O hO power S cs e D p (rvTupleAssignment q) := ⟨dom,hh⟩
    refine ⟨⟨⟨p,dom,hh⟩,hn⟩,p,relation,?_⟩
    exact (A.fieldFiberSupportTags_mem idx zero s p (rvTupleAssignment r)).2 ⟨mem,support⟩
  · rintro ⟨⟨_,hn⟩,p,⟨_,hh⟩,mem⟩
    obtain ⟨inA,support⟩ := (A.fieldFiberSupportTags_mem idx zero s p (rvTupleAssignment r)).1 mem
    have fields : (fun _ : Fin 1 => p .vf 0) = p .vf := by
      funext i
      rw [Fin.fin_one_eq_zero i]
    refine ⟨⟨p .vf 0,?_,hh⟩,support,hn⟩
    rw [fields]
    exact inA

end GeneralizedEuler.Section5
