module

public import Section2.ResidueMap
public import Section2.SortedSyntax

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

end GeneralizedEuler.Section2
