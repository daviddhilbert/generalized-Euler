module

public import Section2.ConvexLanguage
public import Section2.VFLiftSubstructure

/-! Restricting a sorted embedding to the language of valued fields. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w}
  {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure K] [L.Structure F]
  (O : ValuationSubring K) (Q : ValuationSubring F) [L.Structure (Residue O)] [L.Structure (Residue Q)]
  (hO : IsOrderConvex O) (hQ : IsOrderConvex Q) (P : E → RV0 O → RV0 O) (PQ : E → RV0 Q → RV0 Q)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO P))

/-- The old VF sort is a substructure in the field language. -/
@[expose]
def vfReductOfSortedSubstructure : L.Substructure K where
  carrier := S.carrier .vf
  fun_mem f x hx := by
    let b (i) : S.carrier .vf := ⟨x i, hx i⟩
    let as := expandHomogeneousArgs (X := fun s => S.carrier s) b
    have hm := S.closed (.vf f) (fun i => (as i).val) (fun i => (as i).property)
    change Structure.funMap f (homogeneousArgs (fun i => (as i).val)) ∈ S.carrier .vf at hm
    rw [homogeneousArgs_map (X := fun s => S.carrier s) (Y := CanonicalSort O)
      (fun _ z => z.val) as, homogeneousArgs_expand] at hm
    exact hm

variable (e : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))

/-- The old sorted map restricts to an embedding in the field language. -/
def fieldEmbeddingOfSorted : vfReductOfSortedSubstructure O hO P S ↪[L] F where
  toFun := e.toEmbedding .vf
  inj' := (e.toEmbedding .vf).injective
  map_fun' := by
    intro n f x
    let B := vfReductOfSortedSubstructure O hO P S
    let a : Fin n → S.carrier .vf := x
    let as := expandHomogeneousArgs (X := fun s => S.carrier s) a
    have h := e.map_fun (.vf f) as
    change e.toEmbedding .vf (S.structureOn.funMap (.vf f) as) =
      Structure.funMap f (homogeneousArgs (fun i => (e.toEmbedding _).toFun (as i))) at h
    rw [homogeneousArgs_map (fun s => (e.toEmbedding s).toFun) as, homogeneousArgs_expand] at h
    have hf : S.structureOn.funMap (.vf f) as = Structure.funMap (L := L) (M := B) f x := by
      apply Subtype.ext
      change Structure.funMap f (homogeneousArgs (fun i => (as i).val)) =
        B.subtype (Structure.funMap (L := L) (M := B) f x)
      rw [homogeneousArgs_map (X := fun s => S.carrier s) (Y := CanonicalSort O)
        (fun _ z => z.val) as, homogeneousArgs_expand]
      exact (B.subtype.map_fun f x).symm
    rw [hf] at h
    exact h
  map_rel' := by
    intro n r x
    let B := vfReductOfSortedSubstructure O hO P S
    let a : Fin n → S.carrier .vf := x
    let as := expandHomogeneousArgs (X := fun s => S.carrier s) a
    have h := e.map_rel (.vf r) as
    change Structure.RelMap r (homogeneousArgs (fun i => (e.toEmbedding _).toFun (as i))) ↔
      Structure.RelMap r (homogeneousArgs (fun i => (as i).val)) at h
    rw [homogeneousArgs_map (fun s => (e.toEmbedding s).toFun) as, homogeneousArgs_expand,
      homogeneousArgs_map (X := fun s => S.carrier s) (Y := CanonicalSort O)
        (fun _ z => z.val) as, homogeneousArgs_expand] at h
    exact h.trans (B.subtype.map_rel r x)

set_option linter.style.haveILetI false in
/-- Adding the valuation-ring relation leaves the old field carrier and
its closure under function symbols unchanged. -/
@[expose]
def convexReductOfSortedSubstructure :
    letI := convexStructure O L
    (convexLanguage L).Substructure K := by
  letI := convexStructure O L
  letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K := convexStructure_expansion O
  let B := vfReductOfSortedSubstructure O hO P S
  refine ⟨S.carrier .vf, ?_⟩
  intro n f a ha
  change L.Functions n ⊕ ringPredicateLanguage.Functions n at f
  cases f with
  | inl f =>
    change Structure.funMap ((LHom.sumInl : L →ᴸ convexLanguage L).onFunction f) a ∈ S.carrier .vf
    rw [LHom.map_onFunction (LHom.sumInl : L →ᴸ convexLanguage L)]
    exact B.fun_mem f a ha
  | inr f => exact f.elim

set_option linter.style.haveILetI false in
/-- The field restriction of an old sorted embedding preserves the
valued-field language used in Lemma 2.20 and Theorem 2.16. -/
def valuedFieldEmbeddingOfSorted (minusOne : S.carrier .vf)
    (hminus : minusOne.val = -1) (hminus' : e.toEmbedding .vf minusOne = -1) :
    letI := convexStructure O L
    letI := convexStructure Q L
    convexReductOfSortedSubstructure O hO P S ↪[convexLanguage L] F := by
  letI := convexStructure O L
  letI := convexStructure Q L
  letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn K := convexStructure_expansion O
  letI : (LHom.sumInl : L →ᴸ convexLanguage L).IsExpansionOn F := convexStructure_expansion Q
  let B := convexReductOfSortedSubstructure O hO P S
  let C := vfReductOfSortedSubstructure O hO P S
  let f := fieldEmbeddingOfSorted O Q hO hQ P PQ S e
  refine { toFun := e.toEmbedding .vf, inj' := (e.toEmbedding .vf).injective
           map_fun' := ?_, map_rel' := ?_ }
  · intro n g x
    change L.Functions n ⊕ ringPredicateLanguage.Functions n at g
    cases g with
    | inl g =>
      let gc := (LHom.sumInl : L →ᴸ convexLanguage L).onFunction g
      have heq : Structure.funMap (L := convexLanguage L) (M := B) gc x =
          Structure.funMap (L := L) (M := C) g x := by
        apply Subtype.ext
        have h := B.subtype.map_fun gc x
        have hg : Structure.funMap (L := convexLanguage L) (M := K) gc (B.subtype ∘ x) =
            Structure.funMap (L := L) g (B.subtype ∘ x) :=
          (LHom.sumInl : L →ᴸ convexLanguage L).map_onFunction g _
        exact h.trans (hg.trans (C.subtype.map_fun g x).symm)
      change e.toEmbedding .vf (Structure.funMap (L := convexLanguage L) (M := B) gc x) =
        Structure.funMap ((LHom.sumInl : L →ᴸ convexLanguage L).onFunction g)
          ((e.toEmbedding .vf).toFun ∘ x)
      rw [heq, LHom.map_onFunction (LHom.sumInl : L →ᴸ convexLanguage L)]
      exact f.map_fun g x
    | inr g => exact g.elim
  · intro n r x
    change L.Relations n ⊕ ringPredicateLanguage.Relations n at r
    cases r with
    | inl r =>
      let rc := (LHom.sumInl : L →ᴸ convexLanguage L).onRelation r
      have hB := B.subtype.map_rel rc x
      change Structure.RelMap ((LHom.sumInl : L →ᴸ convexLanguage L).onRelation r) (B.subtype ∘ x) ↔
        Structure.RelMap (M := B) rc x at hB
      rw [LHom.map_onRelation (LHom.sumInl : L →ᴸ convexLanguage L)] at hB
      change Structure.RelMap ((LHom.sumInl : L →ᴸ convexLanguage L).onRelation r)
        ((e.toEmbedding .vf).toFun ∘ x) ↔ Structure.RelMap (M := B) rc x
      rw [LHom.map_onRelation (LHom.sumInl : L →ᴸ convexLanguage L)]
      exact (f.map_rel r x).trans ((C.subtype.map_rel r x).symm.trans hB)
    | inr r =>
      cases r
      let rc := (LHom.sumInr : ringPredicateLanguage →ᴸ convexLanguage L).onRelation RingPredicate.mem
      have hB := B.subtype.map_rel rc x
      change Structure.RelMap (L := convexLanguage L) rc ((e.toEmbedding .vf).toFun ∘ x) ↔
        Structure.RelMap (M := B) rc x
      exact (convexStructure_mem Q _).trans
        ((mem_valuationRing_iff_of_sortedEmbedding O hO P Q hQ PQ S e minusOne (x 0)
          hminus hminus').trans ((convexStructure_mem O _).symm.trans hB))

end GeneralizedEuler.Section2
