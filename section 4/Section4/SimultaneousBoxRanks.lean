module

public import Section4.BoxRanks
public import Section4.ScaleAvoidance
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! A finite tuple can attain all the scale ranks simultaneously. When a
coordinate is added, a single exclusion in the largest relevant quotient
suffices for every smaller quotient. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Set
variable {F V I T : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem mkQ_notMem_span_image (H : Submodule F V) (s : Set V) {y : V}
    (h : y ∉ H ⊔ Submodule.span F s) : H.mkQ y ∉ Submodule.span F (H.mkQ '' s) := by
  intro mem
  apply h
  rw [← Submodule.comap_map_mkQ,Submodule.mem_comap,Submodule.map_span]
  exact mem

theorem independent_box_coordinates [Fintype I] (G : Submodule F V) (H : T → Submodule F V)
    (topScale : I → Submodule F V) (active : I → T → Prop) (D : I → Set V)
    (nested : ∀ i j, active i j → H j ≤ topScale i)
    (choosePoint : ∀ i (s : Finset V), ∃ y ∈ D i, (∃ j, active i j) → y ∉ (G ⊔ Submodule.span F (s : Set V)) ⊔ topScale i) :
    ∃ x : I → V, (∀ i, x i ∈ D i) ∧ ∀ j,
      LinearIndepOn F ((G ⊔ H j).mkQ ∘ x) {i | active i j} := by
  classical
  have step (s : Finset I) : ∃ x : I → V, (∀ i ∈ s, x i ∈ D i) ∧ ∀ j,
      LinearIndepOn F ((G ⊔ H j).mkQ ∘ x) {i | i ∈ s ∧ active i j} := by
    induction s using Finset.induction_on with
    | empty => refine ⟨0,by simp,by simp⟩
    | insert i s fresh ih =>
      obtain ⟨x,dom,ind⟩ := ih
      obtain ⟨y,hy,avoid⟩ := choosePoint i (s.image x)
      let z := Function.update x i y
      have agrees {l} (h : l ∈ s) : z l = x l :=
        Function.update_of_ne (fun eq : l = i => fresh (eq ▸ h)) _ _
      refine ⟨z,?_,?_⟩
      · intro l hl
        rcases Finset.mem_insert.mp hl with rfl|h
        · simpa [z] using hy
        · rw [agrees h]; exact dom l h
      · intro j
        let q := (G ⊔ H j).mkQ
        let old : Set I := {l | l ∈ s ∧ active l j}
        have oldInd : LinearIndepOn F (q ∘ z) old :=
          (ind j).congr (fun l hl => congrArg q (agrees hl.1).symm)
        by_cases a : active i j
        · have sub : (q ∘ z) '' old ⊆ q '' ((↑(s.image x)) : Set V) := by
            rintro _ ⟨l,hl,rfl⟩
            exact ⟨x l,Finset.mem_image.mpr ⟨l,hl.1,rfl⟩,congrArg q (agrees hl.1).symm⟩
          have outside : y ∉ (G ⊔ H j) ⊔ Submodule.span F (↑(s.image x) : Set V) := by
            intro mem
            apply avoid ⟨j,a⟩
            exact (sup_le (sup_le (le_sup_left.trans le_sup_left) ((nested i j a).trans le_sup_right))
              (le_sup_right.trans le_sup_left)) mem
          have newInd := oldInd.insert (x := i) (fun mem => mkQ_notMem_span_image _ _ outside
            (Submodule.span_mono sub (by simpa [z,q,Function.comp_def] using mem)))
          convert newInd using 1
          ext l; simp [old, or_and_right]; aesop
        · convert oldInd using 1
          ext l; simp [old]; aesop
  obtain ⟨x,dom,ind⟩ := step Finset.univ
  exact ⟨x,fun i => dom i (Finset.mem_univ _),fun j => by simpa using ind j⟩

end GeneralizedEuler.Section4
