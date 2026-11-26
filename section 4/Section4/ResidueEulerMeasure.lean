module

public import Section4.FiniteFiberEuler
public import Section4.CanonicalRectangles
import all Section4.FiniteFiberEuler
import all Section4.LocalRVMeasure
import all Section4.SignedRectangleFactors
import all Section4.ValuePullback
import all Section2.RVCoordinatePrimitives
import all Section2.RVSplitCoordinates
import all Section2.RVVectorSpace
import all Section2.RVDefinableEquivalence

/-! The unary Euler input used by Question 4.16 is the usual o-minimal
Euler characteristic on the residue field. Fixed-base residue–value
separation transfers it to the positive RV unit line. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false

structure UnaryEuler {K : Type*} (H : Language) [H.Structure K] (B : Set K) where
  weight : ∀ D : Set (Fin 1 → K), B.Definable H D → ℤ
  cut : ∀ {I : Type} [Fintype I] D (hd : B.Definable H D) (d : I → Set (Fin 1 → K))
    (h : ∀ i, B.Definable H (d i)), Pairwise (fun i j => Disjoint (d i) (d j)) →
    (⋃ i, d i) = D → weight D hd = ∑ i, weight (d i) (h i)
  iso : ∀ D E (hd : B.Definable H D) (he : B.Definable H E) (f : D ≃ E),
    B.Definable H {w : Fin 1 ⊕ Fin 1 → K | ∃ x : D, x.val = w ∘ Sum.inl ∧ (f x).val = w ∘ Sum.inr} →
    weight D hd = weight E he

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
  (hO : IsOrderConvex O) {J JH : Language} [J.Structure K] [J.Structure (Residue O)] [JH.Structure (Residue O)]
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P)) (B : Set (Residue O))

def residueTrace {I : Type} (D : Set (I → RV0 O)) : Set (I → Residue O) := {r | residueRV O ∘ r ∈ D}

theorem residue_trace_definable {I : Type} [Finite I] {JG : Language} [JG.Structure O.ValueGroupˣ]
    (G : Set O.ValueGroupˣ) (T : RVValueSection O) (p : F → O.ValueGroupˣ → O.ValueGroupˣ)
    (primitives : RVCoordinateDefinability (L := J) (JG := JG) (JH := JH) hO G B p P)
    (g : F → PositiveField K →* PositiveField K) (agrees : ∀ e, AgreesWithFieldPower O (g e) (P e))
    (clamp : ∀ e t, ¬IsPositiveRV O t → P e t=0)
    (units : ∀ e (x : PositiveField K), O.valuation (x : K)=1 → O.valuation (g e x : K)=1)
    (sec : ∀ e γ, P e (T.representative γ) = T.representative (p e γ))
    (qe : ∀ φ : SortedFormula J F (FullRVVariables S I), ∃ q : SortedFormula J F (FullRVVariables S I), q.IsQF ∧
      ∀ w, q.realize (canonicalStructure (L := J) O hO P) w ↔ φ.realize (canonicalStructure (L := J) O hO P) w)
    (base : ∀ t : S.carrier .rv, (T.encode t.val).1 ∈ G ∧ (T.encode t.val).2 ∈ B)
    (D : Set (I → RV0 O)) (hd : isRVSet _ S D) : B.Definable JH (residueTrace O D) := by
  let Q := T.canonicalCoordinatePresentation primitives g agrees clamp units sec
  have split := Q.separated_rv_pullback S hd qe base (T.separated_decoded_coordinate_graph primitives)
  have slice {Z : Set ((I → O.ValueGroupˣ) × (I → Residue O))} (h : SplitDefinable JG JH G B Z) :
      B.Definable JH ((fun r => ((1 : I → O.ValueGroupˣ),r)) ⁻¹' Z) := by
    induction h with
    | empty => exact Set.definable_empty
    | @insert U V d _ hv _ ih =>
      rw [Set.preimage_union]
      by_cases one : (1 : I → O.ValueGroupˣ) ∈ U
      · rw [Set.mk_preimage_prod_right one]; exact hv.union ih
      · rw [Set.mk_preimage_prod_right_eq_empty one,Set.empty_union]; exact ih
  convert slice split using 1
  ext r
  change (residueRV O ∘ r ∈ D) ↔ (fun i => T.join 1 (r i)) ∈ D
  simp only [T.join_one]; rfl

variable (traceDef : ∀ {I : Type} [Finite I] (D : Set (I → RV0 O)), isRVSet _ S D → B.Definable JH (residueTrace O D))
local notation "M" => canonicalStructure (L := J) O hO P

private def traceEquiv (D : Set (Fin 1 → RV0 O)) (hd : GoodRVSet M S (positiveUnit O hO) D) : residueTrace O D ≃ D := by
  let f (x : residueTrace O D) : D := ⟨residueRV O ∘ x.val,x.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y eq; exact Subtype.ext (funext fun i => residueRV_injective O (congrFun (congrArg Subtype.val eq) i))
  · rintro ⟨x,hx⟩
    have range (i) : x i ∈ Set.range (residueRV O) := by
      have nz := (hd.2 x hx i).1
      have lab := (hd.2 x hx i).2
      rw [range_residueRV]; right; rw [unsignedValue_of_signedLabel O hO _ nz,lab]; rfl
    choose r hr using range
    exact ⟨⟨r,(congrArg (· ∈ D) (funext hr)).mpr hx⟩,Subtype.ext (funext hr)⟩

def positiveUnitEuler (χ : UnaryEuler JH B) : LocalRVMeasure M S (positiveUnit O hO) 1 ℤ where
  weight D hd := χ.weight (residueTrace O D) (traceDef _ hd.1)
  cut D hd d h disj cover := by
    apply χ.cut
    · exact fun i j ne => Disjoint.preimage (residueRV O ∘ ·) (disj ne)
    · rw [← cover]; exact Set.preimage_iUnion.symm
  iso D E hd he equivalence := by
    obtain ⟨f,hf⟩ := equivalence
    let u := traceEquiv O hO P S D hd
    let w := traceEquiv O hO P S E he
    let e := u.trans (f.trans w.symm)
    apply χ.iso _ _ _ _ e
    let G := {p : Fin 1 ⊕ Fin 1 → RV0 O | ∃ a : D, a.val = p ∘ Sum.inl ∧ (f a).val = p ∘ Sum.inr}
    have defG : isRVSet M S G := hf
    let R := {p : Fin 1 ⊕ Fin 1 → Residue O | ∃ a : residueTrace O D, a.val = p ∘ Sum.inl ∧ (e a).val = p ∘ Sum.inr}
    change B.Definable JH R
    refine (show R = residueTrace O G from ?_).symm ▸ traceDef G defG
    apply Set.ext; intro p
    constructor
    · rintro ⟨x,hx,hy⟩
      have eq : w (e x) = f (u x) := w.apply_symm_apply _
      exact ⟨u x,congrArg (residueRV O ∘ ·) hx,(congrArg Subtype.val eq).symm.trans (congrArg (residueRV O ∘ ·) hy)⟩
    · rintro ⟨x,hx,hy⟩
      let a := u.symm x
      have l := congrArg Subtype.val (u.apply_symm_apply x)
      have r := congrArg Subtype.val (w.apply_symm_apply (f x))
      change residueRV O ∘ (w.symm (f x)).val = (f x).val at r
      have ea : e a = w.symm (f x) := congrArg (fun z => w.symm (f z)) (u.apply_symm_apply _)
      exact ⟨a,funext (fun i => residueRV_injective O (congrFun (l.trans hx) i)),
        funext (fun i => residueRV_injective O (by rw [ea]; exact congrFun (r.trans hy) i))⟩

set_option linter.style.haveILetI false in
theorem positiveUnitLine_trace :
    letI := residueLinearOrder O hO
    residueTrace O (positiveUnitLine (J := J) O hO P) = {r : Fin 1 → Residue O | 0 < r 0} := by
  letI := residueLinearOrder O hO
  letI := rvLinearOrder O hO
  have pos (r : Residue O) : IsPositiveRV O (residueRV O r) ↔ 0 < r := by
    rw [isPositiveRV_iff_pos O hO,← residueRV_zero O]
    exact (residueRV_strictMono O hO).lt_iff_lt
  ext x; constructor
  · intro hx
    have ne := hx.1 0
    have eq : signedLabel O hO (residueRV O (x 0)) = 1 := congrFun hx.2 0
    exact (pos _).mp ((signedLabel_pos O hO ne).mp (congrArg Prod.fst eq))
  · intro hx
    have positive i : IsPositiveRV O (residueRV O (x i)) := (pos _).mpr (by simpa [Subsingleton.elim i 0] using hx)
    refine ⟨fun i => (positive i).ne_zero O,funext fun i => Prod.ext ((signedLabel_pos O hO ((positive i).ne_zero O)).mpr (positive i)) ?_⟩
    apply Units.ext
    have u := unsignedValue_of_signedLabel O hO _ ((positive i).ne_zero O)
    exact u.symm.trans (unsignedValue_residueRV_of_ne_zero O (by intro h; exact (positive i).ne_zero O (h ▸ residueRV_zero O)))

def residuePositiveRay := {x : Fin 1 → Residue O | (residueLinearOrder O hO).lt 0 (x 0)}

theorem positiveUnitEuler_line (χ : UnaryEuler JH B)
    (ray : ∀ h : B.Definable JH (residuePositiveRay O hO), χ.weight _ h = -1)
    (good : GoodRVSet M S (positiveUnit O hO) (positiveUnitLine (J := J) O hO P)) :
    (positiveUnitEuler O hO P S B @traceDef χ).weight _ good = -1 := by
  have cg {D E : Set (Fin 1 → Residue O)} (eq : D=E) (hd : B.Definable JH D) (he : B.Definable JH E) :
      χ.weight D hd = χ.weight E he := by subst E; rfl
  have eq : residueTrace O (positiveUnitLine (J := J) O hO P) = residuePositiveRay O hO := positiveUnitLine_trace O hO P
  have defD := traceDef _ good.1
  have defE : B.Definable JH (residuePositiveRay O hO) := eq ▸ defD
  exact (cg eq defD defE).trans (ray defE)

end GeneralizedEuler.Section4
