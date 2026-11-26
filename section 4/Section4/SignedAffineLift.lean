module

public import Section4.FixedBaseAffineLift
import all Section4.ValuePullback
import all Section4.SignedValueGeneration
import all Section4.SignedRectangleFactors
import all Section4.ValuePadding

/-! The commutative square on each signed affine value cell. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) (hO : IsOrderConvex O) {J JG JS : Language}
  [J.Structure K] [J.Structure (Residue O)] [JG.Structure O.ValueGroupˣ] [JS.Structure (SignedValueGroup O)]
  (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (hv : ∀ x, v x = Additive.ofMul (positiveValueMap O x.toMul))
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul =
    P e (positiveRVToRV0 O x.toMul))
  (G : Submodule F (Additive O.ValueGroupˣ)) (A : Set (SignedValueGroup O))
  (reps : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
local instance signedAffineAdditiveStructure : JG.Structure (Additive O.ValueGroupˣ) := inferInstanceAs (JG.Structure O.ValueGroupˣ)
local instance signedAffineSignedStructure : JS.Structure (SignTypeˣ × Additive O.ValueGroupˣ) := inferInstanceAs (JS.Structure (SignedValueGroup O))
variable (interpret : SignedInterpretation (J := JG) (H := JS) (G : Set (Additive O.ValueGroupˣ)) A)
  (defSharp : ∀ {k} {D : Set (Fin k → SignedValueGroup O)}, A.Definable JS D →
    isRVSet _ S (sharp (canonicalStructure (L := J) O hO P) (signedLabel O hO) D))
  (witness : ∀ {n} (D : Set (Fin n → RV0 O)), isRVSet _ S D → D.Nonempty → ∃ x ∈ D, ∀ i, x i ∈ S.carrier .rv)
local notation "model" => canonicalStructure (L := J) O hO P
local notation "lab" => signedLabel O hO
local notation "V" => Additive O.ValueGroupˣ
local notation "sh" => sharp model lab

omit [Module F (Additive (PositiveRV O))] in
include interpret defSharp witness in
theorem old_sign_tuple {k} (b : Fin k → SignTypeˣ) :
    ∃ u : Fin k → S.carrier .rv, (∀ i, (u i).val ≠ 0) ∧ ∀ i, lab (u i).val = (b i,1) := by
  let D := signInsert b '' ((zeroTuple k : Set (Fin k → V)))
  have hd : A.Definable JS D := signed_stratum_definable _ _ @interpret _ _ (zeroTuple_definable G k)
  choose t nt ht using fun i => signedLabel_rep O hO (b i,1)
  have nonempty : (sh D).Nonempty := ⟨t,nt,0,rfl,funext fun i => (ht i).symm⟩
  obtain ⟨u,⟨nu,a,ha,eq⟩,old⟩ := witness _ (defSharp hd) nonempty
  have az : a = 0 := ha
  subst a
  exact ⟨fun i => ⟨_,old i⟩,nu, fun i => (congrFun eq i).symm⟩

include hv hs reps powers interpret defSharp witness in
theorem signed_affine_cell_lift {k} (b c : Fin k → SignTypeˣ)
    (T : (Matrix (Fin k) (Fin k) F)ˣ) (δ : Fin k → G)
    (D : Set (Fin k → V)) (hd : (G : Set V).Definable JG D) :
    ∃ e : sh (signInsert b '' D) ≃ sh (signInsert c '' (affineLift T (Subtype.val ∘ δ) '' D)),
      SortedDefinableOver model S.carrier (rvGraph (fun x => (e x).val)) ∧
      ∀ x, lab ∘ (e x).val = signInsert c (affineLift T (Subtype.val ∘ δ)
        (fun i => Additive.ofMul (lab (x.val i)).2)) := by
  let oneSign : Fin k → SignTypeˣ := fun _ => 1
  let W := affineLift T (Subtype.val ∘ δ) '' D
  have eqPos (B : Set (Fin k → V)) : sh (signInsert oneSign '' B) = positiveSharp O v B :=
    signed_sharp_positive O hO v hv P B
  have hd' : isRVSet model S (sh (signInsert oneSign '' D)) :=
    defSharp (signed_stratum_definable _ _ @interpret oneSign D hd)
  let u i := s (δ i).val
  have vu : v ∘ u = Subtype.val ∘ δ := funext fun i => DFunLike.congr_fun hs (δ i).val
  have pos : ∃ e : sh (signInsert oneSign '' D) ≃ sh (signInsert oneSign '' W),
      SortedDefinableOver model S.carrier (rvGraph fun x => (e x).val) ∧
      ∀ x, (fun i => Additive.ofMul (lab ((e x).val i)).2) = affineLift T (Subtype.val ∘ δ)
        (fun i => Additive.ofMul (lab (x.val i)).2) := by
    rw [eqPos D,eqPos W]
    obtain h := positive_affine_lift O hO P S v hv powers T u (fun i => reps (δ i)) D ((eqPos D) ▸ hd')
    rw [vu] at h
    exact h
  obtain ⟨f,hf,lf⟩ := pos
  have restore (a : Fin k → SignTypeˣ) (B : Set (Fin k → V))
      (hB : isRVSet model S (sh (signInsert oneSign '' B))) :
      ∃ e : sh (signInsert oneSign '' B) ≃ sh (signInsert a '' B),
        SortedDefinableOver model S.carrier (rvGraph fun x => (e x).val) ∧
        ∀ x i, lab ((e x).val i) = (a i,(lab (x.val i)).2) := by
    obtain ⟨r,nr,hr⟩ := old_sign_tuple O hO P S G A @interpret @defSharp @witness a
    exact restore_sign_lift O hO P S a B r nr hr hB
  obtain ⟨p,hp,lp⟩ := restore b D hd'
  obtain ⟨q,hq,lq⟩ := restore c W (rv_equivalent_target_definable ⟨f,hf⟩)
  refine ⟨(p.symm.trans f).trans q,definable_rvGraph_comp (p.symm.trans f) q (definable_rvGraph_comp p.symm f (definable_rvGraph_inverse p hp) hf) hq,?_⟩
  intro x
  let z := p.symm x
  have same (i : Fin k) : (lab (z.val i)).2 = (lab (x.val i)).2 := by
    have h := congrArg Prod.snd (lp z i)
    rw [show p z = x from p.apply_symm_apply x] at h
    exact h.symm
  funext i
  change lab ((q (f z)).val i) = _
  rw [lq]
  apply congrArg (Prod.mk (c i))
  exact (congrFun (lf z) i).trans (congrFun (congrArg (affineLift T (Subtype.val ∘ δ)) (funext same)) i)

end GeneralizedEuler.Section4
