module

public import Section4.ValueStratification
public import Section2.SplitDefinability
import all Section4.ValueFrames
import all Section4.ValueStratification

public section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {J : Language} [J.Structure V] (G : Submodule F V)

theorem definableFun_of_graph {I M : Type*} {J : Language} [J.Structure M] {A : Set M}
    {f : (I → M) → M} (h : A.Definable J (coordinateTermGraph f)) : A.DefinableFun J f := by
  let e : I ⊕ Unit → Option I := Sum.elim some (fun _ => none)
  simpa [Set.DefinableFun,Function.tupleGraph,coordinateTermGraph,e,Function.comp_def,eq_comm] using
    h.preimage_comp e

/-- The language inputs are the graphs of addition and scalar multiplication
on the value module. Constants for translations are already in the base. -/
structure ValueLanguage : Prop where
  add : (G : Set V).DefinableFun J (fun x : Fin 2 → V => x 0 + x 1)
  smul : ∀ c : F, (G : Set V).DefinableFun J (fun x : Unit → V => c • x ())

namespace ValueLanguage
variable {G} (h : ValueLanguage (J := J) G)
include h

theorem addFun {I : Type*} {f g : (I → V) → V}
    (hf : (G : Set V).DefinableFun J f) (hg : (G : Set V).DefinableFun J g) :
    (G : Set V).DefinableFun J (fun x => f x + g x) := by
  let t (x : I → V) := ![f x,g x]
  have ht : (G : Set V).DefinableMap J t := by
    intro i; fin_cases i <;> assumption
  exact h.add.comp ht

theorem row {I : Type*} [Fintype I] (c : I → F) :
    (G : Set V).DefinableFun J (fun x : I → V => ∑ i, c i • x i) := by
  classical
  have sum (l : Finset I) : (G : Set V).DefinableFun J (fun x : I → V => ∑ i ∈ l, c i • x i) := by
    induction l using Finset.induction_on with
    | empty => simpa using J.definableFun_const I G.zero_mem
    | insert i l hi ih =>
      simp only [Finset.sum_insert hi]
      exact h.addFun ((h.smul (c i)).comp (g := fun x _ => x i) (fun _ => Set.DefinableFun.proj J)) ih
  exact sum Finset.univ

theorem frame {r n} (a : ValueFrame G r n) : (G : Set V).DefinableMap J a.eval :=
  fun i => h.addFun (h.row (a.rows i)) (J.definableFun_const _ (a.shift i).property)

theorem range {n} (p : ValuePivot G n) : (G : Set V).Definable J (Set.range p.frame.eval) := by
  let t (x : Fin (n+1) → V) := p.index.removeNth x
  have ht : (G : Set V).DefinableMap J t := fun i => Set.DefinableFun.proj J
  have hg := (Set.DefinableFun.proj (A := (G : Set V)) J (i := p.index)).ofPred_eq
    (h.addFun ((h.row p.coefficients).comp ht) (J.definableFun_const _ p.offset.property))
  convert hg using 1
  ext x; exact p.mem_range x

theorem cut {n l} (p : Fin l → ValuePivot G n) (D : Set (Fin (n+1) → V)) (i : Fin l)
    (hd : (G : Set V).Definable J D) : (G : Set V).Definable J (firstPivot p D i) := by
  let pre := (p i).frame.eval
  let before := {j : Fin l // j < i}
  have a := hd.preimage_map (h.frame (p i).frame)
  have b := Set.definable_iInter_of_finite (fun j : before =>
    (h.range (p j.val)).compl.preimage_map (h.frame (p i).frame))
  convert a.inter b using 1
  ext x; simp [firstPivot,before]

/-- Apply saturation to the first-order formulas defining the complement of
each pivot and the given value set. Finitely many discarded hyperplanes give
exactly the finite-satisfiability test. -/
theorem avoidance
    (realize : ∀ n (Δ : Set (J[[(G : Set V)]].Formula (Fin n))),
      (∀ t : Finset (J[[(G : Set V)]].Formula (Fin n)), (↑t : Set _) ⊆ Δ →
        ∃ x : Fin n → V, ∀ φ ∈ t, φ.Realize x) →
      ∃ x : Fin n → V, ∀ φ ∈ Δ, φ.Realize x) :
    RealizesAffineAvoidance G (fun _ D => (G : Set V).Definable J D) := by
  classical
  intro n D hd finite
  obtain ⟨θ,hθ⟩ := hd
  choose φ hφ using fun p : ValuePivot G n => (h.range p).compl
  let Δ := insert θ (Set.range φ)
  obtain ⟨x,hx⟩ := realize _ Δ (by
    intro t sub
    let J' := {ψ : t // ψ.val ∈ Set.range φ}
    let p (ψ : J') := ψ.property.choose
    let s := Finset.univ.image p
    obtain ⟨x,xd,avoids⟩ := finite s
    refine ⟨x,fun ψ mem => ?_⟩
    rcases sub mem with eq | he
    · subst ψ; rwa [hθ] at xd
    · let j : J' := ⟨⟨ψ,mem⟩,he⟩
      have eq : φ (p j) = ψ := j.property.choose_spec
      rw [← eq]
      have hm : x ∈ (Set.range (p j).frame.eval)ᶜ :=
        avoids _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
      rwa [hφ (p j)] at hm)
  refine ⟨x,?_,fun p => ?_⟩
  · rw [hθ]; exact hx θ (Set.mem_insert _ _)
  · have hr := hx (φ p) (Set.mem_insert_of_mem _ ⟨p,rfl⟩)
    exact show x ∈ (Set.range p.frame.eval)ᶜ from (hφ p).symm ▸ hr

end ValueLanguage
end GeneralizedEuler.Section4
