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
