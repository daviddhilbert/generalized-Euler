module

public import Section3.AtomicProfiles
import all Section3.AtomicProfiles
import all Section2.PowerBounded

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set
variable {k H : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] {L : Language} [L.Structure k]

private def reflectChart (b : Bool) (x : k) := if b then -x else x

omit [IsStrictOrderedRing k] in
private theorem reflected_graph {F : OrderedFieldTerms L} (hF : InterpretsOrderedFieldTerms (A := k) F)
    {h : k → k} (hd : (univ : Set k).Definable₂ L (fieldGraph univ h)) (b c : Bool) :
    (univ : Set k).Definable₂ L (fieldGraph univ (fun x => reflectChart c (h (reflectChart b x)))) := by
  obtain ⟨φ,hφ⟩ := hd
  let P : Set k := univ
  let z : (L[[P]]).Term (Fin 2) := ((L.lhomWithConstants P).onTerm F.zero).relabel Empty.elim
  let var (b : Bool) (j : Fin 2) : (L[[P]]).Term (Fin 2) :=
    if b then ((L.lhomWithConstants P).onTerm F.sub).subst ![z,.var j] else .var j
  have eval (b j) (v : Fin 2 → k) : (var b j).realize v = reflectChart b (v j) := by
    have zero : z.realize v = 0 := by
      simp only [z,Term.realize_relabel,LHom.realize_onTerm]
      rw [show v ∘ Empty.elim = Empty.elim from Subsingleton.elim _ _,hF.zero]
    cases b <;> simp [var,reflectChart,Term.realize_subst,LHom.realize_onTerm,hF.sub,zero]
  refine ⟨φ.subst ![var b 0,var c 1],?_⟩
  ext v
  change (_ ∧ _) ↔ BoundedFormula.Realize (φ.subst _) v default
  rw [BoundedFormula.realize_subst]
  have graph (a : Fin 2 → k) : φ.Realize a ↔ a 1 = h (a 0) := by
    simpa [fieldGraph] using (Set.ext_iff.mp hφ a).symm
  change (_ ∧ _) ↔ φ.Realize _
  rw [graph,and_iff_right (mem_univ _)]
  change _ ↔ (var c 1).realize v = h ((var b 0).realize v)
  rw [eval,eval]
  cases c
  · rfl
  · change v 1 = -_ ↔ -v 1 = _
    constructor <;> intro h <;> simpa using congrArg Neg.neg h

private def reflectedAction {h : k → k} (g : ResidueChartAction L h) (b c : Bool) :
    ResidueChartAction L (fun x => reflectChart c (h (reflectChart b x))) where
  fieldMap := g.fieldMap
  languageMap := g.languageMap
  compatible := g.compatible
  increasing := g.increasing
  origin := reflectChart b g.origin
  direction := g.direction
  nonzeroDirection := g.nonzeroDirection
  targetScale := g.targetScale
  nonzeroScale := g.nonzeroScale
  equivariant x := by
    cases b
    · cases c
      · exact g.equivariant x
      · change -h (g.origin + g.direction*g.fieldMap x) = g.targetScale * g.fieldMap (-h x)
        rw [g.equivariant,map_neg,mul_neg]
    · have eqn : -(-g.origin + g.direction*g.fieldMap x) = g.origin+g.direction*g.fieldMap (-x) := by
        rw [map_neg,mul_neg]; ring
      cases c
      · change h (-(-g.origin+_)) = _
        rw [eqn]; exact g.equivariant (-x)
      · change -h (-(-g.origin+_)) = g.targetScale * g.fieldMap (-h (-x))
        rw [eqn,g.equivariant,map_neg,mul_neg]

private theorem no_reflected_ray (hom : IsOMinimal (K := k) L) (hpb : IsPowerBounded (K := k) L)
    {F : OrderedFieldTerms L} (hF : InterpretsOrderedFieldTerms (A := k) F) {h : k → k}
    (hd : (univ : Set k).Definable₂ L (fieldGraph univ h)) (action : H → ResidueChartAction L h)
    (transitive : ∀ x y, ∃ i, (action i).move x = y) (b c : Bool)
    (inc : StrictMono (fun x => reflectChart c (h (reflectChart b x))))
    (ray : range (fun x => reflectChart c (h (reflectChart b x))) = Ioi 0) : False := by
  apply no_atomic_line_to_ray hom hpb hF inc ray (reflected_graph hF hd b c) (fun i => reflectedAction (action i) b c)
  intro x y
  obtain ⟨i,hi⟩ := transitive (reflectChart b x) (reflectChart b y)
  refine ⟨i,?_⟩
  cases b
  · exact hi
  · change (action i).origin + (action i).direction*(action i).fieldMap (-x) = -y at hi
    change -(action i).origin + (action i).direction*(action i).fieldMap x = y
    rw [map_neg,mul_neg] at hi
    linarith

/-- The affine-line obstruction holds for either half-ray and either
orientation of the induced bijection. Reflecting chart coordinates
preserves both definability and the base-fixing semilinear action. -/
theorem no_atomic_line_to_either_ray (hom : IsOMinimal (K := k) L) (hpb : IsPowerBounded (K := k) L)
    {F : OrderedFieldTerms L} (hF : InterpretsOrderedFieldTerms (A := k) F) {h : k → k}
    (hd : (univ : Set k).Definable₂ L (fieldGraph univ h)) (action : H → ResidueChartAction L h)
    (transitive : ∀ x y, ∃ i, (action i).move x = y) (mono : StrictMono h ∨ StrictAnti h)
    (ray : range h = Ioi 0 ∨ range h = Iio 0) : False := by
  have negRange : range (fun x : k => h (-x)) = range h := neg_surjective.range_comp h
  have negTarget (g : k → k) (hg : range g = Iio 0) : range (fun x => -g x) = Ioi 0 := by
    ext y
    change (∃ x, -g x = y) ↔ 0 < y
    constructor
    · rintro ⟨x,rfl⟩
      exact neg_pos.mpr (hg.subset (mem_range_self x))
    · intro hy
      obtain ⟨x,hx⟩ := hg.symm.subset (show -y ∈ Iio 0 from neg_neg_of_pos hy)
      exact ⟨x,by simp [hx]⟩
  rcases mono with up | down <;> rcases ray with pos | neg
  · exact no_reflected_ray hom hpb hF hd action transitive false false up pos
  · exact no_reflected_ray hom hpb hF hd action transitive true true
      (fun _ _ lt => neg_lt_neg (up (neg_lt_neg lt))) (negTarget _ (negRange.trans neg))
  · exact no_reflected_ray hom hpb hF hd action transitive true false
      (fun _ _ lt => down (neg_lt_neg lt)) (negRange.trans pos)
  · exact no_reflected_ray hom hpb hF hd action transitive false true
      (fun _ _ lt => neg_lt_neg (down lt)) (negTarget _ neg)

end GeneralizedEuler.Section3
