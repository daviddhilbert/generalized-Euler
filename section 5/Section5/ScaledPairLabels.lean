module

public import Section5.TerminalGradedIsomorphism
public import Section5.BalancedContractionClasses

/-! Compare two terminal pairs whose first label is fixed and whose
second labels differ by multiplication by a named nonzero slope. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*} {O : ValuationSubring K} [L.Structure (Residue O)]
  {hO : IsOrderConvex O} {power : E → RV0 O → RV0 O}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO power)}

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "Z" => CanonicalSort O

theorem scaled_pair_terminal_classes
    (A B : RetainedFieldFamily 𝓜 S 0 2)
    (idx : Fin 2 ≃ A.tags) (idy : Fin 2 ≃ B.tags)
    (t r u : S.carrier .rv) (ne : u.val ≠ 0)
    (zt : t.val = 0 ↔ r.val = 0)
    (X Y : Set (RV0 O))
    (a : ∀ q, q ∈ A.terminalLabels idx ↔ q 0 = t.val ∧ q 1 ∈ X)
    (b : ∀ q, q ∈ B.terminalLabels idy ↔ q 0 = r.val ∧ q 1 ∈ Y)
    (range : (fun v => u.val * v) '' X = Y)
    (selA : ∀ i, A.terminalSelect idx i = i)
    (selB : ∀ i, B.terminalSelect idy i = i)
    (zero : S.carrier .rv) (hz : zero.val = 0) :
    A.terminalGradedClass idx zero hz = B.terminalGradedClass idy zero hz := by
  let send (q : Fin 2 → RV0 O) : Fin 2 → RV0 O := Fin.cases r.val (fun _ => u.val * q 1)
  let map (q : A.terminalLabels idx) : B.terminalLabels idy :=
    ⟨send q.val,(b _).2 ⟨rfl,range ▸ Set.mem_image_of_mem _ ((a _).1 q.property).2⟩⟩
  have inj : Function.Injective map := by
    intro x y h
    have lead := congrArg (fun q : B.terminalLabels idy => q.val 1) h
    change u.val * x.val 1 = u.val * y.val 1 at lead
    have z := ((a _).1 x.property).1.trans ((a _).1 y.property).1.symm
    apply Subtype.ext
    funext i
    refine Fin.cases z (fun j => ?_) i
    have eq : j = 0 := Subsingleton.elim _ _
    subst j
    exact rv_mul_left_cancel O ne lead
  have surj : Function.Surjective map := by
    intro y
    obtain ⟨q,hq,he⟩ : y.val 1 ∈ (fun v => u.val * v) '' X := range.symm ▸ ((b _).1 y.property).2
    let values : Fin 2 → RV0 O := Fin.cases t.val (fun _ => q)
    let x : A.terminalLabels idx := ⟨values,(a values).2 ⟨rfl,hq⟩⟩
    refine ⟨x,Subtype.ext ?_⟩
    funext i
    refine Fin.cases ((b _).1 y.property).1.symm (fun j => ?_) i
    have eq : j = 0 := Subsingleton.elim _ _
    subst j
    exact he
  let e := Equiv.ofBijective map ⟨inj,surj⟩
  let V := RVVariables (Fin 2 ⊕ Fin 2)
  let dep : (s : TCsort) → RVVariables (Fin 2) s → V s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  let const : SortedTerm L E (WithBase S.carrier V) .rv := .var (.inl r)
  let slope : SortedTerm L E (WithBase S.carrier V) .rv := .var (.inl u)
  let old : SortedTerm L E (WithBase S.carrier V) .rv := .var (.inr (.inl 1))
  have d := (A.terminalLabels_definable idx).pullback_relabel dep
  have eq₀ := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := V)
    .rv (.inr 0) const
  have eq₁ := SortedDefinableOver.coordinate_eq_term (M := 𝓜) (A := S.carrier) (Var := V)
    .rv (.inr 1) (rvMulTerm slope old)
  have graph : SortedDefinableOver 𝓜 S.carrier (rvGraph (fun q => (e q).val)) := by
    convert d.inter (eq₀.inter eq₁) using 1
    ext v
    have ev : (rvMulTerm slope old).realize 𝓜 (fun s => Sum.elim Subtype.val (v s)) =
        u.val * v .rv (.inl 1) := by rw [realize_rvMulTerm O hO power]; rfl
    change (∃ q : A.terminalLabels idx, q.val = v .rv ∘ Sum.inl ∧ send q.val = v .rv ∘ Sum.inr) ↔
      ((v .rv ∘ Sum.inl) ∈ A.terminalLabels idx ∧ v .rv (.inr 0) = r.val ∧
        v .rv (.inr 1) = (rvMulTerm slope old).realize 𝓜 (fun s => Sum.elim Subtype.val (v s)))
    rw [ev]
    constructor
    · rintro ⟨q,hq,hv⟩
      exact ⟨hq ▸ q.property,(congrFun hv 0).symm,(congrFun hv 1).symm.trans (congrArg (u.val * ·) (congrFun hq 1))⟩
    · rintro ⟨h,h₀,h₁⟩
      refine ⟨⟨_,h⟩,rfl,?_⟩
      funext i
      refine Fin.cases h₀.symm (fun j => ?_) i
      have eq : j = 0 := Subsingleton.elim _ _
      subst j
      exact h₁.symm
  apply A.terminalGradedClass_of_label_iso B idx idy e graph (Equiv.refl _) zero hz
  intro q i
  rw [selA,Equiv.refl_apply,selB,hz]
  change q.val i ≠ 0 ↔ send q.val i ≠ 0
  refine Fin.cases ?_ (fun j => ?_) i
  · change q.val 0 ≠ 0 ↔ r.val ≠ 0
    rw [((a _).1 q.property).1]
    exact not_congr zt
  · have eq : j = 0 := Subsingleton.elim _ _
    subst j
    change q.val 1 ≠ 0 ↔ u.val * q.val 1 ≠ 0
    exact ⟨mul_ne_zero (M₀ := RV0 O) ne,fun nonzero h => nonzero
      ((congrArg (u.val * ·) h).trans (mul_zero (M₀ := RV0 O) _))⟩

end GeneralizedEuler.Section5
