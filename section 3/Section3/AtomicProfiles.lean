module

public import Section3.ResidueChoice
import all Section2.PowerBounded

public section

namespace GeneralizedEuler.Section3

open Set FirstOrder FirstOrder.Language GeneralizedEuler.Section2
variable {k H : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] {L : Language} [L.Structure k]

def residueProfile (h : k → k) (x v s : k) := h (x+s*v) / h x

def describesProfile {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 2)) (h : k → k) (p : Fin n → k) (x v : k) :=
  ∀ s t, φ.Realize (Sum.elim p ![s,t]) ↔ t = residueProfile h x v s

omit [IsStrictOrderedRing k] in
/-- A single scheme suffices. Take a formula for the chart normalized
at an arbitrary origin and turn its finitely many parameters into variables. -/
private theorem some_profile_scheme {h : k → k} {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := k) F) (hn : h 0 ≠ 0)
    (hd : (univ : Set k).Definable₂ L (fieldGraph univ h)) :
    ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 2)) (p : Fin n → k), describesProfile φ h p 0 1 := by
  classical
  obtain ⟨C,_,hC⟩ := definable_iff_finitely_definable.mp (definable_normalized_graph hF hn hd)
  obtain ⟨ψ,hψ⟩ := definable_iff_exists_formula_sum.mp hC
  let e := Fintype.equivFin C
  let p (i : Fin (Fintype.card C)) := (e.symm i).val
  refine ⟨_,ψ.relabel (Sum.map e id),p,fun s t => ?_⟩
  rw [Formula.realize_relabel]
  have assign : Sum.elim p ![s,t] ∘ Sum.map e id = Sum.elim Subtype.val ![s,t] := by
    funext j; rcases j with c | j <;> simp [p]
  rw [assign]
  have rel := (Set.ext_iff.mp hψ ![s,t]).symm
  change ψ.Realize (Sum.elim Subtype.val ![s,t]) ↔ t = h (0+s*1) / h 0
  rw [mul_one,zero_add]
  exact rel.trans (and_iff_right (mem_univ s))

private def feasible {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 2)) (h : k → k) : Set (Fin n → k) :=
  {p | ∃ x v, v ≠ 0 ∧ describesProfile φ h p x v}

omit [IsStrictOrderedRing k] in
/-- The set of all parameter tuples describing a normalized chart at
some origin and in some nonzero direction is first-order in the residue
field after choosing affine coordinates. -/
private theorem feasible_definable {h : k → k} {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := k) F) (hn : ∀ x, h x ≠ 0)
    (hd : (univ : Set k).Definable₂ L (fieldGraph univ h)) {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 2)) :
    (univ : Set k).Definable L (feasible φ h) := by
  obtain ⟨ψ,hψ⟩ := hd
  let P : Set k := univ
  let A := Fin n ⊕ Fin 3
  let B := A ⊕ Fin 2
  let inj := L.lhomWithConstants P
  let x : A := .inr 0
  let v : A := .inr 1
  let z : A := .inr 2
  let zeroT {I : Type} : (L[[P]]).Term I := (inj.onTerm F.zero).relabel Empty.elim
  let times (a b : (L[[P]]).Term B) := (inj.onTerm F.mul).subst ![a,b]
  let minus (a b : (L[[P]]).Term B) := (inj.onTerm F.sub).subst ![a,b]
  let src := minus (.var (.inl x)) (minus zeroT (times (.var (.inr 0)) (.var (.inl v))))
  let dst := times (.var (.inr 1)) (.var (.inl z))
  let rename : Fin n ⊕ Fin 2 → B := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let test := ((inj.onFormula φ).relabel rename).iff (ψ.subst ![src,dst])
  let atOrigin : (L[[P]]).Formula A := ψ.subst ![Term.var x,.var z]
  let nonzero := ((Term.var v).equal zeroT).not
  refine ⟨Formula.iExs (Fin 3) (nonzero ⊓ atOrigin ⊓ Formula.iAlls (Fin 2) test),?_⟩
  ext p
  have graph (w : Fin 2 → k) : ψ.Realize w ↔ w 1 = h (w 0) := by
    simpa [fieldGraph] using (Set.ext_iff.mp hψ w).symm
  have eval0 {I : Type} (w : I → k) : zeroT.realize w = (0 : k) := by
    simp only [zeroT,Term.realize_relabel,LHom.realize_onTerm]
    rw [show w ∘ Empty.elim = Empty.elim from Subsingleton.elim _ _,hF.zero]
  have aux (a : Fin 3 → k) (w : Fin 2 → k) :
      test.Realize (Sum.elim (Sum.elim p a) w) ↔
      (φ.Realize (Sum.elim p w) ↔ w 1 * a 2 = h (a 0 + w 0 * a 1)) := by
    rw [show test = _ from rfl,Formula.realize_iff,Formula.realize_relabel,LHom.realize_onFormula]
    have asn : Sum.elim (Sum.elim p a) w ∘ rename = Sum.elim p w := by funext i; cases i <;> rfl
    rw [asn]
    apply iff_congr Iff.rfl
    change BoundedFormula.Realize (ψ.subst ![src,dst]) _ default ↔ _
    rw [BoundedFormula.realize_subst]
    change ψ.Realize _ ↔ _
    rw [graph]
    simp [src,dst,minus,times,Term.realize_subst,LHom.realize_onTerm,hF.mul,hF.sub,eval0,x,v,z]
  have orig (a : Fin 3 → k) : atOrigin.Realize (Sum.elim p a) ↔ a 2 = h (a 0) := by
    change BoundedFormula.Realize (ψ.subst _) _ default ↔ _
    rw [BoundedFormula.realize_subst]
    exact graph _
  change (∃ x v, v ≠ 0 ∧ describesProfile φ h p x v) ↔ _
  simp only [mem_ofPred_eq,Formula.realize_iExs,Formula.realize_inf,Formula.realize_iAlls,
    nonzero,Formula.realize_not,Formula.realize_equal,Term.realize_var,eval0,v,Sum.elim_inr]
  constructor
  · rintro ⟨a,b,hb,codes⟩
    refine ⟨![a,b,h a],⟨hb,(orig _).mpr rfl⟩,fun w => (aux _ w).mpr ?_⟩
    have he : ![w 0,w 1] = w := by funext j; fin_cases j <;> rfl
    exact (he ▸ codes (w 0) (w 1)).trans (eq_div_iff (hn a))
  · rintro ⟨a,⟨non,eqn⟩,all⟩
    refine ⟨a 0,a 1,non,fun s t => ?_⟩
    have he := (aux a ![s,t]).mp (all ![s,t])
    rw [(orig a).mp eqn] at he
    exact he.trans (eq_div_iff (hn (a 0))).symm


/-- An automorphism acts semilinearly in an affine coordinate on the
source and by a scalar times its residue-field action on the ray. The
scalars and displacements can depend on the automorphism. -/
structure ResidueChartAction (L : Language) [L.Structure k] (h : k → k) where
  fieldMap : k ≃+* k
  languageMap : k ≃[L] k
  compatible : ∀ x, languageMap x = fieldMap x
  increasing : StrictMono fieldMap
  origin : k
  direction : k
  nonzeroDirection : direction ≠ 0
  targetScale : k
  nonzeroScale : targetScale ≠ 0
  equivariant : ∀ x, h (origin+direction*fieldMap x) = targetScale*fieldMap (h x)

namespace ResidueChartAction

omit [IsStrictOrderedRing k]

variable {h : k → k} (g : ResidueChartAction L h)

def move (x : k) := g.origin+g.direction*g.fieldMap x

theorem move_surjective : Function.Surjective g.move := by
  intro y
  obtain ⟨x,hx⟩ := g.fieldMap.surjective ((y-g.origin)/g.direction)
  refine ⟨x,?_⟩
  simp [move,hx,mul_div_cancel₀ _ g.nonzeroDirection]

theorem profile_move (x v s : k) :
    residueProfile h (g.move x) (g.direction*g.fieldMap v) (g.fieldMap s) = g.fieldMap (residueProfile h x v s) := by
  have eqn : g.move x+g.fieldMap s*(g.direction*g.fieldMap v) = g.move (x+s*v) := by
    simp [move]; ring
  rw [residueProfile,eqn]
  simp only [move,g.equivariant,residueProfile,map_div₀]
  exact mul_div_mul_left _ _ g.nonzeroScale

private theorem describes_move {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 2)) (p : Fin n → k) (x v : k) :
    describesProfile φ h p x v ↔ describesProfile φ h (g.fieldMap ∘ p) (g.move x) (g.direction*g.fieldMap v) := by
  have rel (s t : k) :
      φ.Realize (Sum.elim (g.fieldMap ∘ p) ![g.fieldMap s,g.fieldMap t]) ↔ φ.Realize (Sum.elim p ![s,t]) := by
    have he : Sum.elim (g.fieldMap ∘ p) ![g.fieldMap s,g.fieldMap t] = g.languageMap ∘ Sum.elim p ![s,t] := by
      funext j
      rcases j with j | j
      · exact (g.compatible _).symm
      · fin_cases j <;> exact (g.compatible _).symm
    rw [he]
    exact StrongHomClass.realize_formula g.languageMap _
  constructor
  · intro codes u w
    obtain ⟨s,rfl⟩ := g.fieldMap.surjective u
    obtain ⟨t,rfl⟩ := g.fieldMap.surjective w
    rw [rel,codes,g.profile_move]
    exact g.fieldMap.injective.eq_iff.symm
  · intro codes s t
    have H := codes (g.fieldMap s) (g.fieldMap t)
    rw [rel,g.profile_move,g.fieldMap.injective.eq_iff] at H
    exact H

private theorem feasible_move {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 2)) (p : Fin n → k) :
    p ∈ feasible φ h ↔ (g.fieldMap ∘ p) ∈ feasible φ h := by
  constructor
  · rintro ⟨x,v,hv,code⟩
    exact ⟨g.move x,g.direction*g.fieldMap v,mul_ne_zero g.nonzeroDirection ((map_ne_zero g.fieldMap).mpr hv),
      (g.describes_move φ p x v).mp code⟩
  · rintro ⟨y,w,hw,code⟩
    obtain ⟨x,rfl⟩ := g.move_surjective y
    obtain ⟨v,hv⟩ := g.fieldMap.surjective (w/g.direction)
    have he : g.direction*g.fieldMap v = w := by rw [hv,mul_div_cancel₀ _ g.nonzeroDirection]
    have vn : v ≠ 0 := fun h => hw (by simpa [h] using he.symm)
    exact ⟨x,v,vn,(g.describes_move φ p x v).mpr (he.symm ▸ code)⟩

end ResidueChartAction

/-- The affine-line obstruction in 3.34 from transitivity of the
base-fixing automorphisms. A definable set of feasible parameter tuples
has a tuple fixed by all of them. Moving the origin now reproduces the
same normalized profile everywhere on the affine line. -/
theorem no_atomic_line_to_ray (hom : IsOMinimal (K := k) L) (hpb : IsPowerBounded (K := k) L)
    {F : OrderedFieldTerms L} (hF : InterpretsOrderedFieldTerms (A := k) F)
    {h : k → k} (inc : StrictMono h) (ray : range h = Ioi 0)
    (hd : (univ : Set k).Definable₂ L (fieldGraph univ h))
    (action : H → ResidueChartAction L h) (transitive : ∀ x y, ∃ i, (action i).move x = y) : False := by
  have pos (x : k) : 0 < h x := by
    have hx := mem_range_self (f := h) x
    rwa [ray] at hx
  obtain ⟨n,φ,p,hp⟩ := some_profile_scheme hF (pos 0).ne' hd
  obtain ⟨q,⟨a,v,hv,code⟩,fixed⟩ := invariant_residue_tuple hom hF (fun i => (action i).fieldMap)
    (fun i => (action i).increasing) (feasible_definable hF (fun x => (pos x).ne') hd φ)
    ⟨p,0,1,one_ne_zero,hp⟩ (fun i => (action i).feasible_move φ)
  have realizeAt (x : k) : ∃ w ≠ 0, describesProfile φ h q x w := by
    obtain ⟨i,hi⟩ := transitive a x
    let g := action i
    have he : g.fieldMap ∘ q = q := funext (fixed i)
    have moved := (g.describes_move φ q a v).mp code
    rw [he,hi] at moved
    exact ⟨_,mul_ne_zero g.nonzeroDirection ((map_ne_zero g.fieldMap).mpr hv),moved⟩
  obtain ⟨u,hu,base⟩ := realizeAt 0
  apply no_line_to_ray_of_common_profiles hom hpb hF inc ray hd
  intro x
  obtain ⟨w,_,hx⟩ := realizeAt x
  exact ⟨u,w,hu,fun s => (hx s _).mp ((base s _).mpr rfl)⟩

end GeneralizedEuler.Section3
