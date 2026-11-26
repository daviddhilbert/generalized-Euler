module

public import Section4.RVLineCut
public import Section4.ResidueEulerMeasure
public import Section2.RVAgreement
public import Section2.ValuedFieldFormulas
import all Section4.FiniteFiberEuler
import all Section4.ValuePullback
import all Section4.ResidueEulerMeasure
import all Section4.LocalRVMeasure
import all Section4.Objects
import all Section2.RVAgreement
import all Section2.SortedStructure

/-! Cut the actual positive residue fiber before groupification. Both
self-embeddings are interpreted field terms over the original base. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
set_option backward.isDefEq.respectTransparency false

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (O : ValuationSubring K)
    (hO : IsOrderConvex O) {J : Language} [J.Structure K] [J.Structure (Residue O)]
    (P : F → RV0 O → RV0 O) (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
local notation "M" => canonicalStructure (L := J) O hO P
local notation "line" => positiveUnitLine (J := J) O hO P

private def applyUnary (t : J.Term (Fin 1)) (x : Fin 1 → RV0 O) : Fin 1 → RV0 O :=
  fun _ => (liftResidueTerm (E := F) t).realize M (rvTermAssignment (Z := CanonicalSort O) x)

private theorem unary_graph (t : J.Term (Fin 1)) (D : Set (Fin 1 → RV0 O)) (hd : isRVSet M S D) :
    SortedDefinableOver M S.carrier (rvGraph (fun x : D => applyUnary O hO P t x.val)) := by
  let V := RVVariables (Fin 1 ⊕ Fin 1)
  let rename : ∀ s, RVVariables (Fin 1) s → (S.carrier s ⊕ V s)
    | .vf => PEmpty.elim
    | .rv => fun i => .inr (.inl i)
  let lhs := (liftResidueTerm (E := F) t).relabel rename
  let rhs : SortedTerm J F (fun s => S.carrier s ⊕ V s) .rv := .var (.inr (.inr 0))
  let E : Set (Fin 1 ⊕ Fin 1 → RV0 O) := {x | applyUnary O hO P t (x ∘ Sum.inl) 0 = x (.inr 0)}
  have eq : isRVSet M S E := by
    refine ⟨.equal lhs rhs,fun x => ?_⟩
    change _ ↔ lhs.realize M _ = _
    rw [show lhs = (liftResidueTerm (E := F) t).relabel rename from rfl,SortedTerm.realize_relabel]
    have ev : (fun s => Sum.elim Subtype.val (x s) ∘ rename s) =
        rvTermAssignment (Z := CanonicalSort O) (x .rv ∘ Sum.inl) := by
      funext s i; cases s with
      | vf => exact i.elim
      | rv => rfl
    rw [ev]; rfl
  convert (isRVSet_precomp (J := Fin 1 ⊕ Fin 1) Sum.inl hd).inter eq using 1
  ext x
  change (∃ u : D, u.val = x .rv ∘ Sum.inl ∧ applyUnary O hO P t u.val = x .rv ∘ Sum.inr) ↔
    x .rv ∘ Sum.inl ∈ D ∧ _ = x .rv (.inr 0)
  exact ⟨fun ⟨u,hu,he⟩ => ⟨hu ▸ u.property,hu ▸ congrFun he 0⟩,
    fun ⟨h,he⟩ => ⟨⟨_,h⟩,rfl,funext fun i => Subsingleton.elim i 0 ▸ he⟩⟩

private def residueTuple (r : Residue O) : Fin 1 → RV0 O := fun _ => residueRV O r

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem residueTuple_injective : Function.Injective (residueTuple O) :=
  fun _ _ h => residueRV_injective O (congrFun h 0)

private theorem unary_on_residues (t : J.Term (Fin 1)) (r : Residue O) :
    applyUnary O hO P t (residueTuple O r) = residueTuple O (t.realize (fun _ => r)) := by
  funext _
  exact realize_liftResidueTerm O hO P t (fun _ => r)


set_option linter.style.haveILetI false in
private theorem positiveUnitLine_param :
    letI := residueLinearOrder O hO
    line = residueTuple O '' Set.Ioi 0 := by
  letI := residueLinearOrder O hO
  have trace : residueTrace O line = {x : Fin 1 → Residue O | 0 < x 0} := positiveUnitLine_trace (J := J) O hO P
  ext z
  constructor
  · intro hz
    have nz := hz.1 0
    have label := congrFun hz.2 0
    change signedLabel O hO (z 0) = 1 at label
    have range : z 0 ∈ Set.range (residueRV O) := by
      rw [range_residueRV]; right
      rw [unsignedValue_of_signedLabel O hO _ nz,label]; rfl
    obtain ⟨r,hr⟩ := range
    have eq : residueTuple O r = z := funext fun i => by simpa only [residueTuple,Subsingleton.elim i 0] using hr
    have inTrace : (fun _ : Fin 1 => r) ∈ residueTrace O line := by
      change residueTuple O r ∈ line
      rwa [eq]
    exact ⟨r,show (fun _ : Fin 1 => r) ∈ {x : Fin 1 → Residue O | 0 < x 0} from trace ▸ inTrace,eq⟩
  · rintro ⟨r,hr,rfl⟩
    have mem : (fun _ : Fin 1 => r) ∈ {x : Fin 1 → Residue O | 0 < x 0} := hr
    exact show (fun _ : Fin 1 => r) ∈ residueTrace O line from trace.symm ▸ mem


private def residueShifts (terms : OrderedFieldTerms J) :
    J.Term (Fin 1) × J.Term (Fin 1) :=
  let zero := terms.zero.relabel (Empty.elim : Empty → Fin 1)
  let one := terms.one.relabel (Empty.elim : Empty → Fin 1)
  let sub (a b : J.Term (Fin 1)) := terms.sub.subst ![a,b]
  let plus := sub one (sub zero (.var 0))
  (plus,terms.inv.subst (fun _ => plus))

omit [LinearOrder K] [IsStrictOrderedRing K] [J.Structure K] in
private theorem residueShifts_eval (terms : OrderedFieldTerms J)
    (h : InterpretsFieldTerms (K := Residue O) terms.toFieldTerms)
    (one : terms.one.realize (Empty.elim : Empty → Residue O) = 1) (r : Residue O) :
    (residueShifts terms).1.realize (fun _ => r) = 1+r ∧
    (residueShifts terms).2.realize (fun _ => r) = (1+r)⁻¹ := by
  have z := h.zero
  simp [residueShifts,Language.Term.realize_subst,Language.Term.realize_relabel,one,z,
    h.sub,h.inv,Function.comp_def,Matrix.cons_val_zero,Matrix.cons_val_one,Subsingleton.elim (fun _ : Empty => r) Empty.elim]

set_option linter.style.haveILetI false in
theorem positive_residue_line_cut (terms : OrderedFieldTerms J)
    (h : InterpretsFieldTerms (K := Residue O) terms.toFieldTerms)
    (one : terms.one.realize (Empty.elim : Empty → Residue O) = 1)
    (hline : isRVSet M S (sharp M (signedLabel O hO) ({1} : Set (Fin 1 → SignedValueGroup O)))) :
    let U := sharpObject M S (signedLabel O hO) ({1} : Set (Fin 1 → SignedValueGroup O)) hline
    ∃ remainder : RVObject M S 1,
      homogeneousRVClass U = homogeneousRVClass U + homogeneousRVClass U + homogeneousRVClass remainder := by
  letI := residueLinearOrder O hO
  letI := residue_isOrderedRing O hO
  let U := sharpObject M S (signedLabel O hO) ({1} : Set (Fin 1 → SignedValueGroup O)) hline
  have param : U.carrier = residueTuple O '' Set.Ioi 0 := positiveUnitLine_param O hO P
  have rep (x : U.carrier) : ∃ r : Residue O, 0 < r ∧ residueTuple O r = x.val :=
    (congrArg (x.val ∈ ·) param).mp x.property
  let t := residueShifts terms
  let f (x : U.carrier) := applyUnary O hO P t.1 x.val
  let g (x : U.carrier) := applyUnary O hO P t.2 x.val
  have fval (x : U.carrier) (r) (hr : residueTuple O r = x.val) : f x = residueTuple O (1+r) := by
    dsimp only [f]; rw [← hr,unary_on_residues,(residueShifts_eval O terms h one r).1]
  have gval (x : U.carrier) (r) (hr : residueTuple O r = x.val) : g x = residueTuple O (1+r)⁻¹ := by
    dsimp only [g]; rw [← hr,unary_on_residues,(residueShifts_eval O terms h one r).2]
  apply homogeneous_self_embeddings U f g
  · intro x y eq
    obtain ⟨r,_,hr⟩ := rep x; obtain ⟨s,_,hs⟩ := rep y
    rw [fval _ _ hr,fval _ _ hs] at eq
    exact Subtype.ext (hr.symm.trans ((congrArg (residueTuple O) (add_left_cancel (residueTuple_injective O eq))).trans hs))
  · intro x y eq
    obtain ⟨r,_,hr⟩ := rep x; obtain ⟨s,_,hs⟩ := rep y
    rw [gval _ _ hr,gval _ _ hs] at eq
    exact Subtype.ext (hr.symm.trans ((congrArg (residueTuple O) (add_left_cancel (inv_injective (residueTuple_injective O eq)))).trans hs))
  · exact unary_graph O hO P S _ _ hline
  · exact unary_graph O hO P S _ _ hline
  · rintro _ ⟨x,rfl⟩; obtain ⟨r,pos,hr⟩ := rep x
    rw [param,fval _ _ hr]; exact ⟨_,add_pos zero_lt_one pos,rfl⟩
  · rintro _ ⟨x,rfl⟩; obtain ⟨r,pos,hr⟩ := rep x
    rw [param,gval _ _ hr]; exact ⟨_,inv_pos.mpr (add_pos zero_lt_one pos),rfl⟩
  · apply Set.disjoint_left.mpr
    rintro _ ⟨x,rfl⟩ ⟨y,eq⟩
    obtain ⟨r,pr,hr⟩ := rep x; obtain ⟨s,ps,hs⟩ := rep y
    rw [fval _ _ hr,gval _ _ hs] at eq
    have low : (1+s)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (lt_add_of_pos_right _ ps)
    exact ((lt_add_of_pos_right 1 pr).trans_le (residueTuple_injective O eq).ge).not_ge low.le

end GeneralizedEuler.Section4
