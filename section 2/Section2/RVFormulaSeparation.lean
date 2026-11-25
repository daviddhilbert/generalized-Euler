module

public import Section2.RVReduct
public import Section2.SplitDefinability

/-! Primitive separation extends to every RV-only formula and its
term substitutions, with the same value and residue parameters. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z a b u' v' u'' v''

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {JG : Language.{u', v'}} {JH : Language.{u'', v''}}
  {G H : Type*} [JG.Structure G] [JH.Structure H]
  {A : Set G} {B : Set H}

/-- The primitive graphs and relations in the two coordinate reducts.
The encoding can omit invalid coordinate pairs, such as a non-unit
value paired with zero residue. -/
structure RVCoordinatePresentation (M : SortedStructure L E X)
    (JG : Language.{u', v'}) (JH : Language.{u'', v''})
    {G H : Type*} [JG.Structure G] [JH.Structure H] (A : Set G) (B : Set H) where
  encode : X .rv → G × H
  decode : G × H → X .rv
  decode_encode : Function.LeftInverse decode encode
  function_graph : ∀ {ss} (f : FunctionSymbol L E ss .rv) (hs : ∀ i : Fin ss.length, ss.get i = .rv),
    SplitDefinable JG JH A B (splitTermGraph
      (fun x : SplitAssignment G H (Fin ss.length) =>
        encode (M.funMap f (fun i => (hs i).symm ▸ decode (x.1 i, x.2 i)))))
  relation : ∀ {ss} (r : RelationSymbol L ss) (hs : ∀ i : Fin ss.length, ss.get i = .rv),
    SplitDefinable JG JH A B
      {x : SplitAssignment G H (Fin ss.length) |
        M.relMap r (fun i => (hs i).symm ▸ decode (x.1 i, x.2 i))}

namespace SortedTerm.IsRVOnly

variable {Var : TCsort → Type a}

theorem sort_eq {s : TCsort} {t : SortedTerm L E Var s} (h : t.IsRVOnly) : s = .rv := by
  cases h <;> rfl

end SortedTerm.IsRVOnly

variable {M : SortedStructure L E X} (P : RVCoordinatePresentation M JG JH A B)
  {Var : TCsort → Type a} {I : Type b} [Finite I]
  (assign : SplitAssignment G H I → (∀ s, Var s → X s))
  (hassign : ∀ i : Var .rv,
    SplitDefinable JG JH A B (splitTermGraph (fun x => P.encode (assign x .rv i))))

private theorem cast_back {s : TCsort} (h : s = .rv) (x : X s) :
    (h.symm ▸ (h ▸ x : X .rv) : X s) = x := by
  subst s
  rfl

include hassign in
theorem RVCoordinatePresentation.separated_term {s : TCsort} {t : SortedTerm L E Var s}
    (h : t.IsRVOnly) :
    SplitDefinable JG JH A B
      (splitTermGraph (fun x => P.encode (h.sort_eq ▸ t.realize M (assign x)))) := by
  induction h with
  | var i => exact hassign i
  | app f ts ht ih =>
    let hs (i : Fin _) := (ht i).sort_eq
    let g (i : Fin _) (x : SplitAssignment G H I) :=
      P.encode (hs i ▸ (ts i).realize M (assign x))
    have h := SplitDefinable.graph_comp (P.function_graph f hs) g ih
    convert h using 1
    ext x
    have heq (y : SplitAssignment G H I) :
        (fun i => (hs i).symm ▸ P.decode ((splitApply g y).1 i, (splitApply g y).2 i)) =
          (fun i => (ts i).realize M (assign y)) := by
      funext i
      change ((hs i).symm ▸ P.decode (P.encode ((hs i) ▸ (ts i).realize M (assign y)))) = _
      rw [P.decode_encode]
      exact cast_back (hs i) ((ts i).realize M (assign y))
    simp only [splitTermGraph, Set.mem_ofPred, Function.comp_apply, heq, SortedTerm.realize]

include hassign in
private theorem separated_relation {ss : List TCsort} (r : RelationSymbol L ss)
    (ts : SortedArgs (SortedTerm L E Var) ss)
    (ht : ∀ i, (ts i).IsRVOnly) :
    SplitDefinable JG JH A B {x | (SortedFormula.rel r ts).realize M (assign x)} := by
  let hs (i : Fin _) := (ht i).sort_eq
  let g (i : Fin _) (x : SplitAssignment G H I) :=
    P.encode (hs i ▸ (ts i).realize M (assign x))
  have h :=
    (P.relation r hs).preimage_splitApply g (fun i => P.separated_term assign hassign (ht i))
  convert h using 1
  ext x
  have eq : (fun i => (hs i).symm ▸ P.decode ((splitApply g x).1 i, (splitApply g x).2 i)) =
      (fun i => (ts i).realize M (assign x)) := by
    funext i
    change ((hs i).symm ▸ P.decode (P.encode ((hs i) ▸ (ts i).realize M (assign x)))) = _
    rw [P.decode_encode]
    exact cast_back (hs i) ((ts i).realize M (assign x))
  simp only [Set.mem_ofPred, SortedFormula.realize, Set.mem_preimage, eq]

include hassign in
/-- Separation for the RV-only formulas obtained from quantifier
elimination and fixed-base reduction. -/
theorem RVCoordinatePresentation.separated_formula
    {φ : SortedFormula L E Var} (h : φ.IsRVOnly) :
    SplitDefinable JG JH A B {x | φ.realize M (assign x)} := by
  induction h with
  | falsum => exact SeparatedSets.empty
  | @equal t u ht hu =>
    let g : Fin 2 → SplitAssignment G H I → G × H :=
      Fin.cases (fun x => P.encode (t.realize M (assign x)))
        (fun _ x => P.encode (u.realize M (assign x)))
    have hg (i : Fin 2) : SplitDefinable JG JH A B (splitTermGraph (g i)) := by
      refine Fin.cases (P.separated_term assign hassign ht) (fun j => ?_) i
      exact P.separated_term assign hassign hu
    have hd := (SplitDefinable.coordinate_eq (JG := JG) (JH := JH) (A := A) (B := B)
      (0 : Fin 2) 1).preimage_splitApply g hg
    convert hd using 1
    ext x
    change t.realize M (assign x) = u.realize M (assign x) ↔
      P.encode (t.realize M (assign x)) = P.encode (u.realize M (assign x))
    exact P.decode_encode.injective.eq_iff.symm
  | residueNonzero ht => exact separated_relation P assign hassign .residueNonzero _ ht
  | rvLE ht => exact separated_relation P assign hassign .rvLE _ ht
  | @imp phi psi _ _ ihφ ihψ =>
    have he : {x | (SortedFormula.imp phi psi).realize M (assign x)} =
        ({x | phi.realize M (assign x)}ᶜ ∪ {x | psi.realize M (assign x)} :
          Set (SplitAssignment G H I)) := by
      ext x
      simp only [Set.mem_ofPred, SortedFormula.realize, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    exact he.symm ▸ (ihφ.compl.union ihψ)

end GeneralizedEuler.Section2
