module

public import Section2.VFLiftSubstructure
public import Section2.RVReduct
public import Section2.ResidueFiber

/-! Agreement with the old RV embedding in the new-value case of
Theorem 2.16. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w a

section TermAgreement

variable {L : Language.{u, v}} {E : Type w} {X Y Z : TCsort → Type*}
  {M : SortedStructure L E X} {N : SortedStructure L E Y} {H : SortedStructure L E Z}

/-- Agreement with the old map extends from the named generators to all
terms in the intermediate structure. -/
theorem sortedEmbeddings_agree_on_term (S : SortedSubstructure M)
    (old : SortedEmbedding S.structureOn N) (left : SortedEmbedding H M)
    (right : SortedEmbedding H N) {Var : TCsort → Type a} (x : ∀ s, Var s → Z s)
    (h : ∀ s (i : Var s), ∃ hmem : left.toEmbedding s (x s i) ∈ S.carrier s,
      old.toEmbedding s ⟨left.toEmbedding s (x s i), hmem⟩ = right.toEmbedding s (x s i))
    {s : TCsort} (t : SortedTerm L E Var s) :
    ∃ hmem : left.toEmbedding s (t.realize H x) ∈ S.carrier s,
      old.toEmbedding s ⟨left.toEmbedding s (t.realize H x), hmem⟩ =
        right.toEmbedding s (t.realize H x) := by
  classical
  let z (s : TCsort) (i : Var s) : S.carrier s := ⟨left.toEmbedding s (x s i), (h s i).choose⟩
  have hleft : S.inclusion.mapAssignment z = left.mapAssignment x := by
    funext b i
    simp only [SortedEmbedding.mapAssignment_apply, SortedSubstructure.inclusion_apply]
    rfl
  have hright : old.mapAssignment z = right.mapAssignment x := by
    funext b i
    simp only [SortedEmbedding.mapAssignment_apply]
    exact (h b i).choose_spec
  have hval := (left.realize_term x t).trans (hleft ▸ S.inclusion.realize_term z t).symm
  rw [SortedSubstructure.inclusion_apply] at hval
  refine ⟨hval.symm ▸ (t.realize S.structureOn z).property, ?_⟩
  have hz : (⟨_, hval.symm ▸ (t.realize S.structureOn z).property⟩ : S.carrier s) =
      t.realize S.structureOn z := Subtype.ext hval
  rw [hz, old.realize_term, hright, ← right.realize_term]

end TermAgreement

section ResidueTerms

variable {L : Language.{u, v}} {E : Type w} {Var : Type a}

/-- A residue term uses just the translations of the original functional
symbols into RV. -/
def liftResidueTerm : L.Term Var → SortedTerm L E (RVVariables Var) .rv
  | .var i => .var i
  | .func f ts => .app (.residue f) (expandHomogeneousArgs (fun i => liftResidueTerm (ts i)))

abbrev rvTermAssignment {Z : TCsort → Type*} (v : Var → Z .rv) : ∀ s, RVVariables Var s → Z s
  | .vf => PEmpty.elim
  | .rv => v

open FirstOrder.Language in
/-- A lifted residue term evaluated on embedded residues is still in the
embedded residue field and has the original residue as its value. -/
theorem realize_liftResidueTerm {J : Type*} [Field J] [LinearOrder J] [IsStrictOrderedRing J]
    [L.Structure J] (I : ValuationSubring J) [L.Structure (Residue I)]
    (hI : IsOrderConvex I) (power : E → RV0 I → RV0 I) (t : L.Term Var) (v : Var → Residue I) :
    (liftResidueTerm (E := E) t).realize (canonicalStructure I hI power)
        (rvTermAssignment (Z := CanonicalSort I) (residueRV I ∘ v)) = residueRV I (t.realize v) := by
  let M := canonicalStructure (L := L) I hI power
  let a := rvTermAssignment (Z := CanonicalSort I) (residueRV I ∘ v)
  induction t with
  | var i => rfl
  | func f ts ih =>
    let args := expandHomogeneousArgs (fun i => liftResidueTerm (E := E) (ts i))
    change extendResidueOperation I (Structure.funMap f)
      (homogeneousArgs (fun i => (args i).realize M a)) = residueRV I ((Term.func f ts).realize v)
    rw [homogeneousArgs_map (fun _ t => t.realize M a) args, homogeneousArgs_expand]
    have hargs : (fun s t => @SortedTerm.realize L E (RVVariables Var) _ M a s t) .rv ∘
        (fun i => liftResidueTerm (E := E) (ts i)) =
          residueRV I ∘ fun i => (ts i).realize v := funext ih
    rw [hargs, extendResidueOperation_on_residue, Term.realize_func]

end ResidueTerms

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {L : Language.{u, v}} {E : Type w} [L.Structure K] [L.Structure F]
  {O : ValuationSubring K} {Q : ValuationSubring F}
  [L.Structure (Residue O)] [L.Structure (Residue Q)]
  {hO : IsOrderConvex O} {hQ : IsOrderConvex Q}
  {P : E → RV0 O → RV0 O} {PQ : E → RV0 Q → RV0 Q}
  {S : SortedSubstructure (canonicalStructure (L := L) O hO P)}
  (old : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))
  {H : Type*} [MulZeroOneClass H] (source : H →*₀ RV0 O) (target : H →*₀ RV0 Q)

/-- The intermediate leading term has its source image in the old RV
substructure and the old map sends that image to its target image. -/
@[expose]
def RVMapsAgree (x : H) : Prop :=
  ∃ hx : source x ∈ S.carrier .rv, old.toEmbedding .rv ⟨source x, hx⟩ = target x

theorem RVMapsAgree.zero : RVMapsAgree old source target 0 := by
  let z := S.structureOn.funMap (.rvZero : FunctionSymbol L E [] .rv) (fun i => i.elim0)
  have hz : (z : RV0 O) = source 0 := (map_zero source).symm
  refine ⟨hz ▸ z.property, ?_⟩
  have hz' : (⟨source 0, hz ▸ z.property⟩ : S.carrier .rv) = z := Subtype.ext hz.symm
  rw [hz', map_zero target]
  exact old.map_fun .rvZero (fun i => i.elim0)

variable {old source target}

theorem RVMapsAgree.mul {x y : H}
    (hx : RVMapsAgree old source target x) (hy : RVMapsAgree old source target y) :
    RVMapsAgree old source target (x * y) := by
  obtain ⟨hx, hxe⟩ := hx
  obtain ⟨hy, hye⟩ := hy
  let a : SortedArgs (fun s => S.carrier s) [.rv, .rv] :=
    Fin.cases ⟨source x, hx⟩ (fun j => by
      have hj : j = 0 := Fin.fin_one_eq_zero (j : Fin 1)
      subst j
      exact ⟨source y, hy⟩)
  let z := S.structureOn.funMap (.rvMul : FunctionSymbol L E [.rv, .rv] .rv) a
  have hz : (z : RV0 O) = source (x * y) := (map_mul source x y).symm
  refine ⟨hz ▸ z.property, ?_⟩
  have hz' : (⟨source (x * y), hz ▸ z.property⟩ : S.carrier .rv) = z := Subtype.ext hz.symm
  rw [hz', map_mul target]
  have h := old.map_fun .rvMul a
  change old.toEmbedding .rv z =
    old.toEmbedding .rv ⟨source x, hx⟩ * old.toEmbedding .rv ⟨source y, hy⟩ at h
  rw [hxe, hye] at h
  exact h

theorem RVMapsAgree.power (p : E → H → H) (e : E) {x : H}
    (hsource : source (p e x) = P e (source x))
    (htarget : target (p e x) = PQ e (target x))
    (hx : RVMapsAgree old source target x) : RVMapsAgree old source target (p e x) := by
  obtain ⟨hx, hxe⟩ := hx
  let a : SortedArgs (fun s => S.carrier s) [.rv] := fun j => by
    have hj : j = 0 := Fin.fin_one_eq_zero (j : Fin 1)
    subst j
    exact ⟨source x, hx⟩
  let z := S.structureOn.funMap (.power e : FunctionSymbol L E [.rv] .rv) a
  have hz : (z : RV0 O) = source (p e x) := hsource.symm
  refine ⟨hz ▸ z.property, ?_⟩
  have hz' : (⟨source (p e x), hz ▸ z.property⟩ : S.carrier .rv) = z := Subtype.ext hz.symm
  rw [hz', htarget]
  have h := old.map_fun (.power e) a
  change old.toEmbedding .rv z = PQ e (old.toEmbedding .rv ⟨source x, hx⟩) at h
  rw [hxe] at h
  exact h

/-- For a new-value adjunction, agreement on the old coefficients and on
the chosen generator implies agreement on every leading term in its
given monomial normal form. -/
theorem RVMapsAgree.of_monomials (p : E → H → H) (W : Set H) (t : H)
    (hsource : ∀ e, source (p e t) = P e (source t))
    (htarget : ∀ e, target (p e t) = PQ e (target t))
    (hW : ∀ w ∈ W, RVMapsAgree old source target w)
    (ht : RVMapsAgree old source target t)
    (hnormal : ∀ x : H, x ≠ 0 → ∃ w ∈ W, ∃ e : E, x = w * p e t) :
    ∀ x : H, RVMapsAgree old source target x := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact RVMapsAgree.zero old source target
  · obtain ⟨w, hw, e, rfl⟩ := hnormal x hx
    exact (hW w hw).mul (ht.power p e (hsource e) (htarget e))

/-- In the unchanged-value case, agreement on residue generators and old
value representatives implies agreement on the entire intermediate RV sort. -/
theorem RVMapsAgree.of_unchanged_values_and_residue_generation
    {J : Type*} [Field J] [LinearOrder J] [IsStrictOrderedRing J] [L.Structure J]
    (I : ValuationSubring J) [L.Structure (Residue I)] (hI : IsOrderConvex I)
    (power : E → RV0 I → RV0 I)
    (left : SortedEmbedding (canonicalStructure (L := L) I hI power) (canonicalStructure O hO P))
    (right : SortedEmbedding (canonicalStructure (L := L) I hI power) (canonicalStructure Q hQ PQ))
    (src : RV0 I →*₀ RV0 O) (tgt : RV0 I →*₀ RV0 Q)
    (hleft : ∀ x : RV0 I, left.toEmbedding .rv x = src x)
    (hright : ∀ x : RV0 I, right.toEmbedding .rv x = tgt x)
    {Var : Type a} (v : Var → Residue I)
    (hgen : ∀ r : Residue I, ∃ t : L.Term Var, t.realize v = r)
    (hv : ∀ i, RVMapsAgree old src tgt (residueRV I (v i)))
    (W : Set J) (hW : ∀ w ∈ W, RVMapsAgree old src tgt (rv I w))
    (hvalues : ∀ x : J, ∃ w ∈ W, I.valuation w = I.valuation x) :
    ∀ t : RV0 I, RVMapsAgree old src tgt t := by
  have hres (r : Residue I) : RVMapsAgree old src tgt (residueRV I r) := by
    obtain ⟨t, ht⟩ := hgen r
    have hgens : ∀ s (i : RVVariables Var s),
        ∃ hm : left.toEmbedding s (rvTermAssignment (residueRV I ∘ v) s i) ∈ S.carrier s,
          old.toEmbedding s ⟨_, hm⟩ = right.toEmbedding s (rvTermAssignment (residueRV I ∘ v) s i) := by
      intro s i
      cases s with
      | vf => exact i.elim
      | rv =>
        change ∃ hm : left.toEmbedding .rv (residueRV I (v i)) ∈ S.carrier .rv,
          old.toEmbedding .rv ⟨_, hm⟩ = right.toEmbedding .rv (residueRV I (v i))
        rw [hleft, hright]
        exact hv i
    have hg := sortedEmbeddings_agree_on_term S old left right
      (rvTermAssignment (residueRV I ∘ v)) hgens (liftResidueTerm t)
    rw [realize_liftResidueTerm, ht, hleft, hright] at hg
    exact hg
  intro t
  obtain ⟨x, rfl⟩ := rv_surjective I t
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero]
    exact RVMapsAgree.zero old src tgt
  obtain ⟨w, hw, hval⟩ := hvalues x
  have hw0 : w ≠ 0 := (map_ne_zero I.valuation).mp (hval.trans_ne ((map_ne_zero I.valuation).mpr hx))
  obtain ⟨r, _, hr⟩ := rv_factor_residue_of_same_value I hw0 hval.symm
  rw [hr]
  exact (hW w hw).mul (hres r)

/-- Agreement on the intermediate leading terms gives the sorted lift
with the specified VF embedding and exactly the old RV map. -/
theorem exists_vfLift_of_RV_agreement
    (B : L.Substructure K) (field : B ↪[L] F) (rep : B → H)
    (hs : ∀ x, source (rep x) = rv O x.val) (ht : ∀ x, target (rep x) = rv Q (field x))
    (ha : ∀ x, RVMapsAgree old source target (rep x)) :
    ∃ (hB : ∀ x ∈ B, rv O x ∈ S.carrier .rv)
      (j : SortedEmbedding (enlargeVF O hO P S B hB).structureOn
        (canonicalStructure (L := L) Q hQ PQ)),
      (∀ x : B, (j.toEmbedding .vf).toFun x = field x) ∧
      (∀ t : S.carrier .rv, (j.toEmbedding .rv).toFun t = old.toEmbedding .rv t) := by
  have hB (x : K) (hx : x ∈ B) : rv O x ∈ S.carrier .rv := by
    obtain ⟨h, _⟩ := ha ⟨x, hx⟩
    exact hs ⟨x, hx⟩ ▸ h
  have hcomm (x : B) : old.toEmbedding .rv ⟨rv O x.val, hB x x.property⟩ = rv Q (field x) := by
    obtain ⟨hm, he⟩ := ha x
    have hx : (⟨rv O x.val, hB x x.property⟩ : S.carrier .rv) =
        ⟨source (rep x), hm⟩ := Subtype.ext (hs x).symm
    rw [hx, he, ht]
  let j := liftVFEmbedding O hO P Q hQ PQ S B hB old field hcomm
  exact ⟨hB, j, liftVFEmbedding_vf_apply O hO P Q hQ PQ S B hB old field hcomm,
    liftVFEmbedding_rv_apply O hO P Q hQ PQ S B hB old field hcomm⟩

end GeneralizedEuler.Section2
