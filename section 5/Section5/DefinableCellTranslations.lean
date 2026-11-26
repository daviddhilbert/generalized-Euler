module

public import Section5.BalancedCells
public import Section5.DefinableRelativeTranslations

/-! The two product forms of a balanced cell come from actual
fixed-base relatively unary bijections. -/

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

local notation "𝓜" => canonicalStructure (L := L) O hO power
local notation "X" => CanonicalSort O

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[expose] def fieldPairAssignment : fieldAssignment 2 X ≃ K × K where
  toFun a := (a .vf 0,a .vf 1)
  invFun p := fieldTupleAssignment (Fin.cases p.1 (fun _ => p.2))
  left_inv a := fieldAssignment_ext (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have h : j = 0 := Subsingleton.elim _ _
      subst j
      rfl)
  right_inv _ := rfl

theorem field_pair_translation
    (i j : Fin 2) (ne : i ≠ j)
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (C : Set (K × K)) (defC : SortedDefinableOver 𝓜 S.carrier (fieldPairAssignment O ⁻¹' C))
    (D : Set K) (f : K → K)
    (dom : ∀ a : fieldAssignment 2 X, fieldPairAssignment O a ∈ C → a .vf i ∈ D)
    (defF : DefinableRelation 𝓜 S.carrier (fun (x y : fieldAssignment 1 X) =>
      x .vf 0 ∈ D ∧ f (x .vf 0) = y .vf 0)) :
    let A := fieldPairAssignment O ⁻¹' C
    ∃ (B : Set (fieldAssignment 2 X)) (e : MixedGraphIso 𝓜 S A B),
      FixesOutside e {j} ∧ ∀ a : A,
        (e.equiv a).val .vf = Function.update (a.val .vf) j (a.val .vf j - f (a.val .vf i)) := by
  intro A
  let p : Fin 1 → Fin 2 := fun _ => i
  let P : Set (fieldAssignment 1 X) := {u | u .vf 0 ∈ D}
  let c (x : P) := f (x.val .vf 0)
  have inP (a : fieldAssignment 2 X) (ha : a ∈ A) : projectFields p (fieldTupleAssignment (a .vf)) ∈ P :=
    dom a ha
  have g : DefinableRelation 𝓜 S.carrier (fun a (b : fieldAssignment 1 X) =>
      ∃ h : a ∈ P, c ⟨a,h⟩ = b .vf 0) :=
    defF.congr (fun _ _ => ⟨fun ⟨h,e⟩ => ⟨h,e⟩,fun ⟨h,e⟩ => ⟨h,e⟩⟩)
  obtain ⟨e,fix,ev⟩ := relative_translation_iso O hO power S p j (fun _ => ne) F minusOne hm hF
    A defC P c inP g
  refine ⟨_,e,fix,?_⟩
  intro a
  exact congrFun (ev a) .vf

theorem balanced_cell_definable_product_forms
    (F : FieldTerms (convexLanguage L))
    (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F)
    (c : K) (r : O.ValueGroup) (B : Set K) (f g : K → K) (t : RV0 O) (u : RV O)
    (affine : RVAffineOn O (openDisc O c r) f u)
    (small : unsignedValue O (oppositeParadigm O t u) < r)
    (target : ∀ p ∈ positionedCell O (openDisc O c r) f t, p.2 ∈ B)
    (inv : ∀ b ∈ B, g b ∈ openDisc O c r ∧ f (g b) = b)
    (defC : SortedDefinableOver 𝓜 S.carrier
      (fieldPairAssignment O ⁻¹' positionedCell O (openDisc O c r) f t))
    (defF : DefinableRelation 𝓜 S.carrier (fun (x y : fieldAssignment 1 X) =>
      x .vf 0 ∈ openDisc O c r ∧ f (x .vf 0) = y .vf 0))
    (defG : DefinableRelation 𝓜 S.carrier (fun (x y : fieldAssignment 1 X) =>
      x .vf 0 ∈ B ∧ g (x .vf 0) = y .vf 0)) :
    let A := fieldPairAssignment O ⁻¹' positionedCell O (openDisc O c r) f t
    ∃ (C D : Set (fieldAssignment 2 X)) (left : MixedGraphIso 𝓜 S A C) (right : MixedGraphIso 𝓜 S A D),
      FixesOutside left {1} ∧ FixesOutside right {0} ∧
      fieldPairAssignment O '' C = openDisc O c r ×ˢ (rv O ⁻¹' {t}) ∧
      fieldPairAssignment O '' D = (rv O ⁻¹' {oppositeParadigm O t u}) ×ˢ B := by
  intro A
  let cell := positionedCell O (openDisc O c r) f t
  obtain ⟨C,e,ef,ee⟩ := field_pair_translation O hO power S 0 1 (by decide) F minusOne hm hF
    cell defC (openDisc O c r) f (fun _ ha => ha.1) defF
  obtain ⟨D,d,df,de⟩ := field_pair_translation O hO power S 1 0 (by decide) F minusOne hm hF
    cell defC B g (fun a ha => target (fieldPairAssignment O a) ha) defG
  let pair := fieldPairAssignment O
  have leftPair (a : A) : pair (e.equiv a).val = ((pair a.val).1,(pair a.val).2 - f (pair a.val).1) := by
    apply Prod.ext
    · exact congrFun (ee a) 0
    · exact congrFun (ee a) 1
  have rightPair (a : A) : pair (d.equiv a).val = ((pair a.val).1 - g (pair a.val).2,(pair a.val).2) := by
    apply Prod.ext
    · exact congrFun (de a) 0
    · exact congrFun (de a) 1
  have imageOf {C : Set (fieldAssignment 2 X)} (e : MixedGraphIso 𝓜 S A C) (f : K × K → K × K)
      (eval : ∀ a : A, pair (e.equiv a).val = f (pair a.val)) : pair '' C = f '' cell := by
    ext p
    constructor
    · rintro ⟨a,ha,ep⟩
      obtain ⟨x,hx⟩ := e.equiv.surjective ⟨a,ha⟩
      refine ⟨pair x.val,x.property,?_⟩
      rw [← eval x,hx]
      exact ep
    · rintro ⟨p,hp,rfl⟩
      let x : A := ⟨pair.symm p,by change pair (pair.symm p) ∈ cell; rwa [pair.apply_symm_apply]⟩
      refine ⟨(e.equiv x).val,(e.equiv x).property,?_⟩
      rw [eval]
      exact congrArg f (pair.apply_symm_apply p)
  refine ⟨C,D,e,d,ef,df,?_,?_⟩
  · rw [imageOf e (fun p => (p.1,p.2 - f p.1)) leftPair]
    exact positionedCell_translate O _ _ _
  · rw [imageOf d (fun p => (p.1 - g p.2,p.2)) rightPair]
    exact positionedCell_translate_first O B affine small target inv

end GeneralizedEuler.Section5
