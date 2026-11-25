module

public import Section3.AffineLine
import all Section2.PowerBounded
public import Section2.ValuedFieldFormulas

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  {L : Language} [L.Structure k]

/-- A bounded nonempty definable unary set has a supremum in its own
field, even when the ordered field is non-Archimedean. -/
theorem exists_lub_of_ominimal (hom : IsOMinimal (K := k) L) {S : Set k}
    (hd : (univ : Set k).Definable₁ L S) (hne : S.Nonempty) (hb : BddAbove S) :
    ∃ a, IsLUB S a := by
  classical
  obtain ⟨cells,hcell,rfl⟩ := hom S hd
  clear hd
  induction cells using Finset.induction with
  | empty => simp at hne
  | insert c cs hcs ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left] at *
    by_cases hc : c.Nonempty
    · have hbounded : BddAbove c := hb.mono subset_union_left
      have csup : ∃ a, IsLUB c a := by
        rcases hcell c (Or.inl rfl) with rfl | ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
        · exact (not_bddAbove_univ hbounded).elim
        · exact ⟨_,isLUB_singleton⟩
        · exact ⟨_,isLUB_Iio⟩
        · exact (not_bddAbove_Ioi a hbounded).elim
        · exact ⟨_,isLUB_Ioo (nonempty_Ioo.mp hc)⟩
      by_cases hs : (⋃ a ∈ cs, a).Nonempty
      · obtain ⟨b,hb⟩ := ih (fun a ha => hcell _ (Or.inr ha)) hs (hb.mono subset_union_right)
        obtain ⟨a,ha⟩ := csup
        exact ⟨_,ha.union hb⟩
      · rw [not_nonempty_iff_eq_empty.mp hs, union_empty]
        exact csup
    · have he := not_nonempty_iff_eq_empty.mp hc
      rw [he,empty_union] at hne hb ⊢
      exact ih (fun a ha => hcell _ (Or.inr ha)) hne hb

private def ratioTail (E : k → k) (g : PositiveField k →* PositiveField k) (b : k) : Set k :=
  {q | ∃ x : PositiveField k, b < x.val ∧ E x.val = q * (g x).val}

private theorem ratioTail_definable {E : k → k} {g : PositiveField k →* PositiveField k}
    {F : OrderedFieldTerms L} (hF : InterpretsOrderedFieldTerms (A := k) F)
    (hE : (univ : Set k).Definable₂ L (fieldGraph univ E))
    (hg : (univ : Set k).Definable₂ L (powerGraph g)) (b : k) :
    (univ : Set k).Definable₁ L (ratioTail E g b) := by
  obtain ⟨φ,hφ⟩ := hE
  obtain ⟨ψ,hψ⟩ := hg
  let P : Set k := univ
  let x : (L[[P]]).Term (Fin 1 ⊕ Fin 2) := .var (.inr 0)
  let y : (L[[P]]).Term (Fin 1 ⊕ Fin 2) := .var (.inr 1)
  let q : (L[[P]]).Term (Fin 1 ⊕ Fin 2) := .var (.inl 0)
  let prod := ((L.lhomWithConstants P).onTerm F.mul).subst ![q,y]
  let bound : (L[[P]]).Term (Fin 1 ⊕ Fin 2) := (L.con (⟨b,mem_univ _⟩ : P)).term
  let above := ((L.lhomWithConstants P).onRelation F.le).formula ![x,bound]
  refine ⟨Formula.iExs (Fin 2) (above.not ⊓ ψ.subst ![x,y] ⊓ φ.subst ![x,prod]),?_⟩
  ext v
  change (∃ a : PositiveField k, b < a.val ∧ E a.val = v 0 * (g a).val) ↔ _
  have evalOrder (s : Fin 2 → k) : above.Realize (Sum.elim v s) ↔ s 0 ≤ b := by
    rw [show above = _ from rfl, Formula.realize_rel, LHom.map_onRelation, hF.le]
    rfl
  have prodVal (s : Fin 2 → k) : prod.realize (Sum.elim v s) = v 0 * s 1 := by
    simp [prod,Term.realize_subst,LHom.realize_onTerm,hF.mul,y,q]
  have ep (t : Fin 2 → k) : φ.Realize t ↔ t 1 = E (t 0) := by
    simpa [fieldGraph] using (Set.ext_iff.mp hφ t).symm
  have gp (t : Fin 2 → k) : ψ.Realize t ↔ ∃ h : 0 < t 0, t 1 = (g ⟨t 0,h⟩).val :=
    (Set.ext_iff.mp hψ t).symm
  have subeval (χ : (L[[P]]).Formula (Fin 2)) (ts : Fin 2 → (L[[P]]).Term (Fin 1 ⊕ Fin 2))
      (s : Fin 2 → k) : Formula.Realize (χ.subst ts) (Sum.elim v s) ↔ χ.Realize (fun i => (ts i).realize (Sum.elim v s)) :=
    BoundedFormula.realize_subst
  simp only [mem_ofPred_eq, Formula.realize_iExs, Formula.realize_inf,Formula.realize_not,
    evalOrder,not_le,subeval,ep,gp]
  constructor
  · rintro ⟨a,ha,he⟩
    refine ⟨![a.val,(g a).val],⟨ha,⟨a.property,rfl⟩⟩,?_⟩
    change prod.realize _ = E a.val
    rw [prodVal]
    exact he.symm
  · rintro ⟨s,⟨hb,hp,he⟩,ht⟩
    refine ⟨⟨s 0,hp⟩,hb,?_⟩
    change prod.realize _ = E (s 0) at ht
    rw [prodVal] at ht
    exact ht.symm.trans (congrArg (v 0 * ·) he)

/-- Lemma 3.34. For a power bound g, the ratio E(x)/g(x) along a
sufficiently positive tail is at most one. Doubling x more than doubles
that ratio, contradicting its positive definable supremum. -/
theorem no_definable_exponential (hom : IsOMinimal (K := k) L)
    (hpb : IsPowerBounded (K := k) L) {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := k) F) (E : k → k)
    (hdef : (univ : Set k).Definable₂ L (fieldGraph univ E))
    (pos : ∀ x, 0 < E x) (cofinal : ∀ c, ∃ b, ∀ x > b, c < E x)
    (law : ∀ x y, E (x+y) = E x * E y) : False := by
  obtain ⟨g,hg,b,hb⟩ := hpb E hdef
  let two : PositiveField k := ⟨2, by norm_num⟩
  obtain ⟨a,ha⟩ := cofinal (2*(g two).val)
  let B := max 0 (max a b)
  have B0 : 0 ≤ B := le_max_left _ _
  have Ba : a ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have Bb : b ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  let S := ratioTail E g B
  have member (x : PositiveField k) (hx : B < x.val) : E x.val / (g x).val ∈ S :=
    ⟨x,hx,(div_mul_cancel₀ _ (g x).property.ne').symm⟩
  let x₀ : PositiveField k := ⟨B+1,by linarith⟩
  have h₀ := member x₀ (lt_add_one B)
  have bound : (1 : k) ∈ upperBounds S := by
    rintro q ⟨x,hx,he⟩
    have h := hb x (Bb.trans_lt hx)
    rw [abs_of_pos (pos _),he] at h
    exact (le_of_mul_le_mul_right (h.trans_eq (one_mul _).symm) (g x).property)
  obtain ⟨m,hm⟩ := exists_lub_of_ominimal hom (ratioTail_definable hF hdef hg B)
    ⟨_,h₀⟩ ⟨1,bound⟩
  have hmpos := (div_pos (pos x₀.val) (g x₀).property).trans_le (hm.1 h₀)
  obtain ⟨q,⟨x,hx,he⟩,hmq,_⟩ := hm.exists_between (show m/2 < m by linarith)
  let z := two * x
  have hz : z.val = x.val + x.val := by change 2*x.val = _; ring
  have hBz : B < z.val := hz ▸ (by linarith [x.property])
  have hsup := hm.1 (member z hBz)
  have hv : (g z).val = (g two).val * (g x).val := congrArg Subtype.val (map_mul g two x)
  have hratio : E z.val / (g z).val = E x.val / (g two).val * q := by
    rw [hz,law,hv]
    apply (div_eq_iff (mul_ne_zero (g two).property.ne' (g x).property.ne')).mpr
    calc
      E x.val * E x.val = E x.val * (q * (g x).val) := congrArg (E x.val * ·) he
      _ = _ := by field_simp [(g two).property.ne']
  have htwo : 2 < E x.val / (g two).val := (lt_div_iff₀ (g two).property).mpr (ha _ (Ba.trans_lt hx))
  have hq : 0 < q := by linarith
  rw [hratio] at hsup
  linarith [mul_lt_mul_of_pos_right htwo hq]

omit [IsStrictOrderedRing k] in
/-- Normalize the graph in residue coordinates by its value at the
origin. The parameter is allowed in the residue structure after choosing
affine coordinates on the source line and target ray. -/
theorem definable_normalized_graph {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := k) F) {h : k → k} (hn : h 0 ≠ 0)
    (hd : (univ : Set k).Definable₂ L (fieldGraph univ h)) :
    (univ : Set k).Definable₂ L (fieldGraph univ (fun z => h z / h 0)) := by
  obtain ⟨φ,hφ⟩ := hd
  let P : Set k := univ
  let c : (L[[P]]).Term (Fin 2) := (L.con (⟨h 0,mem_univ _⟩ : P)).term
  let y : (L[[P]]).Term (Fin 2) := .var 1
  let prod := ((L.lhomWithConstants P).onTerm F.mul).subst ![y,c]
  refine ⟨φ.subst ![.var 0,prod],?_⟩
  ext v
  have graph (t : Fin 2 → k) : φ.Realize t ↔ t 1 = h (t 0) := by
    simpa [fieldGraph] using (Set.ext_iff.mp hφ t).symm
  have hp : prod.realize v = v 1 * h 0 := by
    simp [prod,Term.realize_subst,LHom.realize_onTerm,hF.mul,y,c]
  change (v 0 ∈ univ ∧ v 1 = h (v 0) / h 0) ↔ _
  rw [and_iff_right (mem_univ _)]
  have substEval : Formula.Realize (φ.subst ![.var 0,prod]) v ↔
      φ.Realize (fun i => (![.var 0,prod] i).realize v) := BoundedFormula.realize_subst
  rw [mem_ofPred_eq,substEval,graph]
  change _ ↔ prod.realize v = h (v 0)
  rw [hp]
  exact eq_div_iff hn

/-- A line-to-ray chart with common profiles is impossible. Orient the
source coordinate so the chart increases. Surjectivity onto the positive
ray gives cofinality even over a non-Archimedean residue field. -/
theorem no_line_to_ray_of_common_profiles (hom : IsOMinimal (K := k) L)
    (hpb : IsPowerBounded (K := k) L) {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := k) F) {h : k → k} (inc : StrictMono h)
    (ray : range h = Ioi 0) (hd : (univ : Set k).Definable₂ L (fieldGraph univ h))
    (profiles : ∀ y, ∃ v w : k, v ≠ 0 ∧
      ∀ s, h (0 + s*v) / h 0 = h (y+s*w) / h y) : False := by
  have pos (x : k) : 0 < h x := by
    have hx := mem_range_self (f := h) x
    rwa [ray] at hx
  have law := (exponential_of_common_profiles inc.injective (fun x => (pos x).ne') profiles).2.2
  apply no_definable_exponential hom hpb hF _ (definable_normalized_graph hF (pos 0).ne' hd)
    (fun x => div_pos (pos x) (pos 0)) _ law
  intro c
  obtain ⟨u,hu⟩ := exists_gt (max 0 (c*h 0))
  obtain ⟨b,hb⟩ : u ∈ range h := ray.symm ▸ ((le_max_left _ _).trans_lt hu : 0 < u)
  refine ⟨b,fun x hx => (lt_div_iff₀ (pos 0)).mpr ?_⟩
  exact ((le_max_right _ _).trans_lt hu).trans (hb ▸ inc hx)

end GeneralizedEuler.Section3
