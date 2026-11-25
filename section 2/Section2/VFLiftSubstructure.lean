module

public import Section2.GeneratedSubstructure
public import Mathlib.ModelTheory.Substructures
public import Mathlib.Tactic.FinCases

/-! Enlarging only the VF sort in a common-lift step of Theorem 2.16
and Lemma 2.20. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language.{u, v}} {E : Type w}
  [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : E → RV0 O → RV0 O)

abbrev vfLiftCarrier
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P)) (B : L.Substructure K) :
    ∀ s, Set (CanonicalSort O s)
  | .vf => B
  | .rv => S.carrier .rv

private theorem homogeneousArgs_mem {X : TCsort → Type*} (C : ∀ s, Set (X s))
    {s : TCsort} {n : ℕ} (a : SortedArgs X (List.replicate n s))
    (ha : ∀ i, a i ∈ C ((List.replicate n s).get i)) :
    ∀ i, homogeneousArgs a i ∈ C s := by
  let b : SortedArgs (fun t => C t) (List.replicate n s) := fun i => ⟨a i, ha i⟩
  have h := homogeneousArgs_map (X := fun t => C t) (Y := X) (fun _ => Subtype.val) b
  intro i
  have hi := congrFun h i
  change homogeneousArgs a i = (homogeneousArgs b i).val at hi
  rw [hi]
  exact (homogeneousArgs b i).property

/-- Replacing VF by a larger field substructure is legitimate as soon as
its leading terms already lie in the old RV sort. -/
@[expose]
def enlargeVF
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P)) (B : L.Substructure K)
    (hB : ∀ x ∈ B, rv O x ∈ S.carrier .rv) :
    SortedSubstructure (canonicalStructure (L := L) O hO P) where
  carrier := vfLiftCarrier O hO P S B
  closed := by
    intro ss s f a ha
    have oldMem {ss : List TCsort} (a : SortedArgs (CanonicalSort O) ss)
        (ha : ∀ i, a i ∈ vfLiftCarrier O hO P S B (ss.get i))
        (hs : ∀ i : Fin ss.length, ss.get i = .rv) :
        ∀ i, a i ∈ S.carrier (ss.get i) := by
      intro i
      have same (t : TCsort) (ht : t = .rv) :
          vfLiftCarrier O hO P S B t = S.carrier t := by
        subst t
        rfl
      have hi := ha i
      rw [same _ (hs i)] at hi
      exact hi
    cases f with
    | vf f =>
      exact B.fun_mem f (homogeneousArgs a) (homogeneousArgs_mem (vfLiftCarrier O hO P S B) a ha)
    | rv =>
      exact hB (a 0) (ha 0)
    | rvZero => exact S.closed .rvZero a (oldMem a ha (fun i => i.elim0))
    | rvOne => exact S.closed .rvOne a (oldMem a ha (fun i => i.elim0))
    | rvMul => exact S.closed .rvMul a (oldMem a ha (fun i => by fin_cases i <;> rfl))
    | rvInv => exact S.closed .rvInv a (oldMem a ha (fun i => by fin_cases i; rfl))
    | power e => exact S.closed (.power e) a (oldMem a ha (fun i => by fin_cases i; rfl))
    | residue f =>
      exact S.closed (.residue f) a
        (oldMem a ha (fun i => by simp only [List.get_eq_getElem, List.getElem_replicate]))

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [L.Structure F]
  (Q : ValuationSubring F) [L.Structure (Residue Q)] (hQ : IsOrderConvex Q)
  (PQ : E → RV0 Q → RV0 Q)

private abbrev liftSortEmbedding
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (B : L.Substructure K) (hB : ∀ x ∈ B, rv O x ∈ S.carrier .rv)
    (old : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))
    (field : B ↪[L] F) :
    ∀ s, (enlargeVF O hO P S B hB).carrier s ↪ CanonicalSort Q s
  | .vf => ⟨field, field.injective⟩
  | .rv => old.toEmbedding .rv

set_option linter.style.haveILetI false in
/-- A field extension can be joined to the old RV map when all leading
terms of the extended field are already named and the two maps agree
on them. The RV part of the resulting embedding is exactly the old one. -/
def liftVFEmbedding
    (S : SortedSubstructure (canonicalStructure (L := L) O hO P))
    (B : L.Substructure K) (hB : ∀ x ∈ B, rv O x ∈ S.carrier .rv)
    (old : SortedEmbedding S.structureOn (canonicalStructure (L := L) Q hQ PQ))
    (field : B ↪[L] F)
    (hRV : ∀ x : B, old.toEmbedding .rv ⟨rv O (x : K), hB x x.property⟩ =
      rv Q (field x)) :
    SortedEmbedding (enlargeVF O hO P S B hB).structureOn
      (canonicalStructure (L := L) Q hQ PQ) where
  toEmbedding := liftSortEmbedding O hO P Q hQ PQ S B hB old field
  map_fun := by
    intro ss s f a
    have pureRV {ss : List TCsort} (f : FunctionSymbol L E ss .rv)
        (a : SortedArgs (fun s => (enlargeVF O hO P S B hB).carrier s) ss)
        (hss : ∀ i : Fin ss.length, ss.get i = .rv) :
        (liftSortEmbedding O hO P Q hQ PQ S B hB old field .rv).toFun
          ((enlargeVF O hO P S B hB).structureOn.funMap f a) =
          (canonicalStructure (L := L) Q hQ PQ).funMap f
            (fun i => (liftSortEmbedding O hO P Q hQ PQ S B hB old field _).toFun (a i)) := by
      let aOld : SortedArgs (fun t => S.carrier t) ss := fun i => ⟨(a i).val, by
        have same (t : TCsort) (ht : t = .rv) :
            (enlargeVF O hO P S B hB).carrier t = S.carrier t := by
          subst t
          rfl
        exact Eq.mp (congrArg (fun C => (a i).val ∈ C) (same _ (hss i)))
          (a i).property⟩
      have hleft : S.structureOn.funMap f aOld =
          (enlargeVF O hO P S B hB).structureOn.funMap f a := by
        apply Subtype.ext
        rfl
      have hright :
          (fun i => (old.toEmbedding _).toFun (aOld i)) =
            (fun i => (liftSortEmbedding O hO P Q hQ PQ S B hB old field _).toFun (a i)) := by
        funext i
        have same (t : TCsort) (ht : t = .rv)
            (b : (enlargeVF O hO P S B hB).carrier t) (c : S.carrier t)
            (heq : b.val = c.val) :
            old.toEmbedding t c =
              (liftSortEmbedding O hO P Q hQ PQ S B hB old field t).toFun b := by
          subst t
          obtain rfl := Subtype.ext heq
          rfl
        exact same _ (hss i) (a i) (aOld i) rfl
      rw [← hright]
      exact hleft ▸ old.map_fun f aOld
    cases f with
    | vf f =>
      have arg := homogeneousArgs_map
        (X := fun t => (enlargeVF O hO P S B hB).carrier t) (Y := CanonicalSort O)
        (fun _ => Subtype.val) a
      have arg' := homogeneousArgs_map
        (X := fun t => (enlargeVF O hO P S B hB).carrier t) (Y := CanonicalSort Q)
        (fun t => (liftSortEmbedding O hO P Q hQ PQ S B hB old field t).toFun) a
      have hfun : (enlargeVF O hO P S B hB).structureOn.funMap (.vf f) a =
          Language.Structure.funMap (L := L) (M := B) f (homogeneousArgs a) := by
        apply Subtype.ext
        change Language.Structure.funMap (L := L) f (homogeneousArgs (fun i => (a i).val)) =
          (B.subtype (Language.Structure.funMap (L := L) (M := B) f (homogeneousArgs a)))
        rw [arg]
        exact (B.subtype.map_fun f (homogeneousArgs a)).symm
      change field ((enlargeVF O hO P S B hB).structureOn.funMap (.vf f) a) =
        Language.Structure.funMap (L := L) f
          (homogeneousArgs (fun i => (liftSortEmbedding O hO P Q hQ PQ S B hB old field _).toFun (a i)))
      rw [hfun, arg']
      exact field.map_fun f _
    | rv => exact hRV (a 0)
    | rvZero => exact pureRV .rvZero a (fun i => i.elim0)
    | rvOne => exact pureRV .rvOne a (fun i => i.elim0)
    | rvMul => exact pureRV .rvMul a (fun i => by fin_cases i <;> rfl)
    | rvInv => exact pureRV .rvInv a (fun i => by fin_cases i; rfl)
    | power e => exact pureRV (.power e) a (fun i => by fin_cases i; rfl)
    | residue f =>
      exact pureRV (.residue f) a (fun i => by simp only [List.get_eq_getElem, List.getElem_replicate])
  map_rel := by
    intro ss r a
    cases r with
    | vf r =>
      have arg := homogeneousArgs_map
        (X := fun t => (enlargeVF O hO P S B hB).carrier t) (Y := CanonicalSort O)
        (fun _ => Subtype.val) a
      have arg' := homogeneousArgs_map
        (X := fun t => (enlargeVF O hO P S B hB).carrier t) (Y := CanonicalSort Q)
        (fun t => (liftSortEmbedding O hO P Q hQ PQ S B hB old field t).toFun) a
      change Language.Structure.RelMap (L := L) r
        (homogeneousArgs (fun i => (liftSortEmbedding O hO P Q hQ PQ S B hB old field _).toFun (a i))) ↔
        Language.Structure.RelMap (L := L) r (homogeneousArgs (fun i => (a i).val))
      rw [arg, arg']
      exact (field.map_rel r (homogeneousArgs a)).trans (B.subtype.map_rel r _).symm
    | residueNonzero =>
      let args : SortedArgs (fun t => S.carrier t) [.rv] := fun i => by
        have hi : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
        subst i
        exact a 0
      exact old.map_rel .residueNonzero args
    | rvLE =>
      let args : SortedArgs (fun t => S.carrier t) [.rv, .rv] :=
        Fin.cases (a 0) (fun j => by
          have hj : j = 0 := Fin.fin_one_eq_zero (j : Fin 1)
          subst j
          exact a 1)
      have h := old.map_rel .rvLE args
      change (rvLinearOrder Q hQ).le (old.toEmbedding .rv (a 0))
          (old.toEmbedding .rv (a 1)) ↔
        (rvLinearOrder O hO).le (a 0).val (a 1).val at h
      exact h

end GeneralizedEuler.Section2
