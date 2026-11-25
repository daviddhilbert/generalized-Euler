module

public import Section2.ResidueMap
public import Section2.ValuedFieldFormulas

/-! Embeddings between canonical two-sorted expansions. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {L : Language.{u, v}} {E : Type w} [L.Structure K] [L.Structure F]
  (O : ValuationSubring K) (P : ValuationSubring F)
  [L.Structure (Residue O)] [L.Structure (Residue P)]

/-- Reducing a named power commutes with an ordered valued-field
embedding that preserves the corresponding field power. -/
theorem mapRV_commutes_with_power (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (f : K →+* F) (hf : RespectsValuationRing O P f) (hmono : StrictMono f)
    (g : PositiveField K →* PositiveField K) (g' : PositiveField F →* PositiveField F)
    (Q : RV0 O → RV0 O) (Q' : RV0 P → RV0 P)
    (hQ : AgreesWithFieldPower O g Q) (hQ' : AgreesWithFieldPower P g' Q')
    (hzero : ∀ t, ¬IsPositiveRV O t → Q t = 0)
    (hzero' : ∀ t, ¬IsPositiveRV P t → Q' t = 0)
    (hg : ∀ (x : PositiveField K) (y : PositiveField F), (y : F) = f x →
      f (g x : K) = (g' y : F)) (t : RV0 O) :
    mapRV O P f hf (Q t) = Q' (mapRV O P f hf t) := by
  obtain ⟨x, rfl⟩ := rv_surjective O t
  by_cases hx : 0 < x
  · have hy : 0 < f x := by simpa only [map_zero f] using hmono hx
    let x' : PositiveField K := ⟨x, hx⟩
    let y' : PositiveField F := ⟨f x, hy⟩
    have h : f (g x' : K) = (g' y' : F) := hg x' y' rfl
    rw [hQ x', mapRV_rv, h, mapRV_rv]
    exact (hQ' y').symm
  · have hy : ¬ 0 < f x := fun h => hx (hmono.lt_iff_lt.mp ((map_zero f).symm ▸ h))
    rw [hzero _ ((isPositiveRV_rv_iff O hO).not.mpr hx), mapRV_zero, mapRV_rv,
      hzero' _ ((isPositiveRV_rv_iff P hP).not.mpr hy)]

private def canonicalEmbeddingSort (i : K ↪[L] F) (f : K →+* F)
    (hf : RespectsValuationRing O P f) :
    ∀ s, CanonicalSort O s ↪ CanonicalSort P s
  | .vf => ⟨i, i.injective⟩
  | .rv => mapRV O P f hf

/-- If the field powers restrict to a valued subfield, the leading-term
powers on that subfield descend from the ambient operations. -/
theorem existsUnique_leadingTermPower_of_valued_embedding
    (f : K →+* F) (hf : RespectsValuationRing O P f) (horder : StrictMono f)
    (g : PositiveField K →* PositiveField K) (g' : PositiveField F →* PositiveField F)
    (Q' : RV0 P → RV0 P) (hQ' : AgreesWithFieldPower P g' Q')
    (hg : ∀ (x : PositiveField K) (y : PositiveField F), (y : F) = f x →
      f (g x : K) = (g' y : F)) :
    ∃! Q : RV0 O → RV0 O, AgreesWithFieldPower O g Q ∧ (∀ t, ¬IsPositiveRV O t → Q t = 0) := by
  apply existsUnique_leadingTermPower_of_same_representatives O g
  have hm (x : PositiveField K) :
      mapRV O P f hf (rv O (g x : K)) = Q' (mapRV O P f hf (rv O (x : K))) := by
    have hx : 0 < f (x : K) := by simpa only [map_zero f] using horder x.property
    let y : PositiveField F := ⟨f (x : K), hx⟩
    rw [mapRV_rv, mapRV_rv, hg x y rfl]
    exact (hQ' y).symm
  intro x y he
  apply (mapRV O P f hf).injective
  rw [hm x, hm y, he]

set_option linter.style.haveILetI false in
/-- A pair embedding compatible with the field language, residue operations,
and powers induces an embedding of the reviewed canonical structures. -/
def canonicalEmbedding (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (PO : E → RV0 O → RV0 O) (PP : E → RV0 P → RV0 P)
    (i : K ↪[L] F) (f : K →+* F) (hi : ∀ x, i x = f x)
    (hf : RespectsValuationRing O P f) (hfOrder : StrictMono f)
    (hRes : ∀ {n} (g : L.Functions n) (a : Fin n → Residue O),
      mapResidue O P f hf (Language.Structure.funMap (L := L) g a) =
        Language.Structure.funMap (L := L) g (mapResidue O P f hf ∘ a))
    (hPow : ∀ e t, mapRV O P f hf (PO e t) = PP e (mapRV O P f hf t)) :
    SortedEmbedding (canonicalStructure (L := L) O hO PO) (canonicalStructure (L := L) P hP PP) where
  toEmbedding := canonicalEmbeddingSort O P i f hf
  map_fun := by
    intro ss s g a
    cases g with
    | vf g =>
      change i (Language.Structure.funMap (L := L) g (homogeneousArgs a)) =
        Language.Structure.funMap (L := L) g (homogeneousArgs (fun j => (canonicalEmbeddingSort O P i f hf _).toFun (a j)))
      rw [homogeneousArgs_map (X := CanonicalSort O) (Y := CanonicalSort P)
        (fun s => (canonicalEmbeddingSort O P i f hf s).toFun) a]
      exact i.map_fun g _
    | rvZero => exact mapRV_zero O P f hf
    | rvOne => exact mapRV_one O P f hf
    | rvMul => exact mapRV_mul O P f hf _ _
    | rvInv => exact mapRV_inv O P f hf _
    | residue g =>
      change mapRV O P f hf (extendResidueOperation O (Language.Structure.funMap (L := L) g) (homogeneousArgs a)) =
        extendResidueOperation P (Language.Structure.funMap (L := L) g)
          (homogeneousArgs (fun j => (canonicalEmbeddingSort O P i f hf _).toFun (a j)))
      rw [homogeneousArgs_map (X := CanonicalSort O) (Y := CanonicalSort P)
        (fun s => (canonicalEmbeddingSort O P i f hf s).toFun) a]
      exact mapRV_extendResidueOperation O P f hf _ _ (hRes g) _
    | power e => exact hPow e _
    | rv =>
      change mapRV O P f hf (rv O (a 0)) = rv P (i (a 0))
      rw [mapRV_rv, hi]
  map_rel := by
    intro ss g a
    cases g with
    | vf g =>
      change Language.Structure.RelMap (L := L) g
        (homogeneousArgs (fun j => (canonicalEmbeddingSort O P i f hf _).toFun (a j))) ↔
          Language.Structure.RelMap (L := L) g (homogeneousArgs a)
      rw [homogeneousArgs_map (X := CanonicalSort O) (Y := CanonicalSort P)
        (fun s => (canonicalEmbeddingSort O P i f hf s).toFun) a]
      exact i.map_rel g _
    | residueNonzero => exact mapRV_value_one_iff O P f hf _
    | rvLE =>
      letI := rvLinearOrder O hO
      letI := rvLinearOrder P hP
      exact (mapRV_strictMono O P hO hP f hf hfOrder).le_iff_le

/-- A field embedding preserves the positive powers when it is
elementary and both models use the same parameter-free graph formulas. -/
theorem fieldPower_agrees_of_elementary
    (i : K ↪ₑ[L] F) (g : PositiveField K →* PositiveField K)
    (g' : PositiveField F →* PositiveField F) (graph : L.Formula (Fin 2))
    (hgraph : ∀ x, graph.Realize x ↔ totalFieldPower g (x 0) = x 1)
    (hgraph' : ∀ x, graph.Realize x ↔ totalFieldPower g' (x 0) = x 1)
    (x : PositiveField K) (y : PositiveField F) (hy : (y : F) = i x) :
    i (g x : K) = (g' y : F) := by
  let a : Fin 2 → K := ![(x : K), (g x : K)]
  have ha : graph.Realize a := (hgraph a).mpr (totalFieldPower_positive g x)
  have hb := (hgraph' (i ∘ a)).mp ((i.map_formula graph a).mpr ha)
  change totalFieldPower g' (i x) = i (g x : K) at hb
  rw [← hy, totalFieldPower_positive] at hb
  exact hb.symm

/-- A positive field power whose total graph is parameter-free restricts
to every elementary submodel, with the same defining graph. -/
theorem exists_fieldPower_of_elementary
    (i : K ↪ₑ[L] F) (f : K →+* F) (hi : ∀ x, i x = f x) (hmono : StrictMono f)
    (g' : PositiveField F →* PositiveField F) (graph : L.Formula (Fin 2))
    (hgraph' : ∀ x, graph.Realize x ↔ totalFieldPower g' (x 0) = x 1) :
    ∃ g : PositiveField K →* PositiveField K,
      ∀ x, graph.Realize x ↔ totalFieldPower g (x 0) = x 1 := by
  classical
  let fpos (x : PositiveField K) : PositiveField F :=
    ⟨f x, (map_zero f) ▸ hmono x.property⟩
  have hex (x : K) : ∃ y : K, graph.Realize ![x, y] := by
    let φ := (graph.relabel (fun j : Fin 2 => if j = 0 then Sum.inl () else Sum.inr ())).iExs Unit
    have heF : φ.Realize (i ∘ fun _ : Unit => x) := by
      apply Language.Formula.realize_iExs.mpr
      refine ⟨fun _ => totalFieldPower g' (i x), ?_⟩
      rw [Language.Formula.realize_relabel]
      have he : (Sum.elim (i ∘ fun _ : Unit => x) (fun _ : Unit => totalFieldPower g' (i x)) ∘
          (fun j : Fin 2 => if j = 0 then Sum.inl () else Sum.inr ())) =
          ![i x, totalFieldPower g' (i x)] := by
        funext j
        fin_cases j <;> rfl
      rw [he, hgraph']
      rfl
    obtain ⟨y, hy⟩ := Language.Formula.realize_iExs.mp
      ((i.map_formula φ (fun _ => x)).mp heF)
    rw [Language.Formula.realize_relabel] at hy
    have hy' : (Sum.elim (fun _ : Unit => x) y ∘
        (fun j : Fin 2 => if j = 0 then Sum.inl () else Sum.inr ())) = ![x, y ()] := by
      funext j
      fin_cases j <;> rfl
    exact ⟨y (), hy' ▸ hy⟩
  have out (x : Fin 2 → K) (h : graph.Realize x) :
      totalFieldPower g' (f (x 0)) = f (x 1) := by
    have he := (hgraph' (i ∘ x)).mp ((i.map_formula graph x).mpr h)
    change totalFieldPower g' (i (x 0)) = i (x 1) at he
    rwa [hi, hi] at he
  let val (x : K) := (hex x).choose
  have hv (x : K) : totalFieldPower g' (f x) = f (val x) :=
    out ![x, val x] (hex x).choose_spec
  have hpos (x : PositiveField K) : 0 < val (x : K) := by
    have h := hv (x : K)
    rw [show f (x : K) = (fpos x : F) from rfl, totalFieldPower_positive] at h
    apply hmono.lt_iff_lt.mp
    rw [map_zero, ← h]
    exact (g' (fpos x)).property
  let p (x : PositiveField K) : PositiveField K := ⟨val x, hpos x⟩
  have hmap (x : PositiveField K) : f (p x : K) = (g' (fpos x) : F) :=
    (hv (x : K)).symm.trans (totalFieldPower_positive g' (fpos x))
  have fone : fpos 1 = 1 := Subtype.ext (map_one f)
  have fmul (x y : PositiveField K) : fpos (x * y) = fpos x * fpos y :=
    Subtype.ext (map_mul f (x : K) (y : K))
  let g : PositiveField K →* PositiveField K :=
    { toFun := p
      map_one' := Subtype.ext (f.injective (by
        rw [hmap, fone, map_one g']
        exact (map_one f).symm))
      map_mul' := fun x y => Subtype.ext (f.injective (by
        change f (p (x * y) : K) = f ((p x : K) * (p y : K))
        rw [hmap, fmul, map_mul g', map_mul f, hmap, hmap]
        rfl)) }
  refine ⟨g, ?_⟩
  intro x
  have hg (a : K) : totalFieldPower g a = val a := by
    by_cases ha : 0 < a
    · let a' : PositiveField K := ⟨a, ha⟩
      exact totalFieldPower_positive g a'
    · have hz : ¬ 0 < f a := by
        rw [← map_zero f, hmono.lt_iff_lt]
        exact ha
      have h := hv a
      rw [totalFieldPower_of_not_pos g' hz] at h
      rw [totalFieldPower_of_not_pos g ha]
      exact f.injective ((map_zero f).trans h)
  rw [hg]
  constructor
  · intro hx
    exact f.injective ((hv _).symm.trans (out _ hx))
  · intro hx
    have he : x = ![x 0, val (x 0)] := by
      funext j
      fin_cases j
      · rfl
      · exact hx.symm
    rw [he]
    exact (hex (x 0)).choose_spec

/-- Keeping the same field powers on a valued subfield transfers
preservation of positive valuation units to that subfield. -/
theorem fieldPower_preserves_units_of_valued_embedding
    (f : K →+* F) (hf : RespectsValuationRing O P f) (hmono : StrictMono f)
    (g : PositiveField K →* PositiveField K) (g' : PositiveField F →* PositiveField F)
    (hg : ∀ (x : PositiveField K) (y : PositiveField F), (y : F) = f x →
      f (g x : K) = (g' y : F))
    (hunit : ∀ y : PositiveField F, P.valuation (y : F) = 1 → P.valuation (g' y : F) = 1)
    (x : PositiveField K) (hx : O.valuation (x : K) = 1) :
    O.valuation (g x : K) = 1 := by
  let y : PositiveField F := ⟨f x, (map_zero f) ▸ hmono x.property⟩
  have hv (z : K) : O.valuation z = 1 ↔ P.valuation (f z) = 1 := by
    simpa only [map_one] using (valuation_eq_map_iff O P f hf z 1).symm
  exact (hv _).mpr ((hg x y rfl).symm ▸ hunit y ((hv _).mp hx))

/-- Canonical expansion of a valued-field embedding. Elementarity on
the field preserves the named powers, and the residue embedding
preserves the extended residue primitives. -/
theorem exists_canonicalEmbedding_of_elementary_field
    (hO : IsOrderConvex O) (hP : IsOrderConvex P)
    (PO : E → RV0 O → RV0 O) (PP : E → RV0 P → RV0 P)
    (i : K ↪ₑ[L] F) (f : K →+* F) (hi : ∀ x, i x = f x)
    (hf : RespectsValuationRing O P f) (hfOrder : StrictMono f)
    (res : Residue O ↪[L] Residue P) (hr : ∀ r, res r = mapResidue O P f hf r)
    (g : E → PositiveField K →* PositiveField K) (g' : E → PositiveField F →* PositiveField F)
    (graph : E → L.Formula (Fin 2))
    (hgraph : ∀ e (v : Fin 2 → K), (graph e).Realize v ↔ totalFieldPower (g e) (v 0) = v 1)
    (hgraph' : ∀ e (v : Fin 2 → F), (graph e).Realize v ↔ totalFieldPower (g' e) (v 0) = v 1)
    (hPO : ∀ e, AgreesWithFieldPower O (g e) (PO e))
    (hPP : ∀ e, AgreesWithFieldPower P (g' e) (PP e))
    (hzeroO : ∀ e t, ¬IsPositiveRV O t → PO e t = 0)
    (hzeroP : ∀ e t, ¬IsPositiveRV P t → PP e t = 0) :
    ∃ e : SortedEmbedding (canonicalStructure (L := L) O hO PO) (canonicalStructure P hP PP),
      (∀ x, e.toEmbedding .vf x = i x) ∧ ∀ t, e.toEmbedding .rv t = mapRV O P f hf t := by
  have hRes : ∀ {n} (symbol : L.Functions n) (a : Fin n → Residue O),
      mapResidue O P f hf (Language.Structure.funMap symbol a) =
        Language.Structure.funMap symbol (mapResidue O P f hf ∘ a) := by
    intro n symbol a
    rw [← hr, res.map_fun]
    congr 1
    exact funext (fun i => hr (a i))
  have hPow (e : E) (t : RV0 O) : mapRV O P f hf (PO e t) = PP e (mapRV O P f hf t) := by
    apply mapRV_commutes_with_power O P hO hP f hf hfOrder (g e) (g' e) (PO e) (PP e)
      (hPO e) (hPP e) (hzeroO e) (hzeroP e) _ t
    intro x y h
    rw [← hi]
    exact fieldPower_agrees_of_elementary i (g e) (g' e) (graph e) (hgraph e) (hgraph' e)
      x y (h.trans (hi _).symm)
  exact ⟨canonicalEmbedding O P hO hP PO PP i.toEmbedding f hi hf hfOrder hRes hPow,
    fun _ => rfl, fun _ => rfl⟩

end GeneralizedEuler.Section2
