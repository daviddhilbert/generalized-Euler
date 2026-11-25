module

public import Section3.AtomicIntervals
public import Section2.DefinableEndDiscs
import all Section3.AtomicIntervals
import all Section2.ValuativeInterval

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K : Type*} [LinearOrder K]

theorem firstComponent_eq_component {U : Set K} {x : K} (hx : x ∈ firstComponent U) :
    firstComponent U = ordConnectedComponent U x := by
  have conv : (firstComponent U).OrdConnected := by
    refine ⟨fun {a} ha {b} hb z hz => ⟨hb.2 a ha.1 z hz.1 hz.2,?_⟩⟩
    exact fun c hc y hcy hyz => hb.2 c hc y hcy (hyz.trans hz.2)
  refine (subset_ordConnectedComponent hx (fun _ h => h.1)).antisymm ?_
  intro y hy
  refine ⟨ordConnectedComponent_subset hy,fun a ha z haz hzy => ?_⟩
  rcases le_total z x with h | h
  · exact hx.2 a ha z haz h
  · exact ordConnectedComponent_subset ((inferInstance : (ordConnectedComponent U x).OrdConnected).out
      (self_mem_ordConnectedComponent.mpr hx.1) hy ⟨h,hzy⟩)

variable [Field K] (O : ValuationSubring K) {L : Language} [L.Structure K]

/-- Every HNF component is definable over the original parameters.
Extract its first component in the order, delete it, and iterate on the
remaining finite decomposition. No representative point becomes a parameter. -/
theorem fixed_base_holly_components (order : L.Relations 2)
    (hLE : ∀ v : Fin 2 → K, Structure.RelMap order v ↔ v 0 ≤ v 1)
    {P U : Set K} (dU : P.Definable₁ L U) {cells : Finset (Set K)}
    (hnf : IsHollyDecomposition O U cells) : ∀ C ∈ cells, P.Definable₁ L C := by
  classical
  induction cells using (measure Finset.card).wf.induction generalizing U with
  | h cells ih =>
    intro C hc
    have un : U.Nonempty := by
      obtain ⟨x,hx⟩ := (hnf.1 C hc).1
      exact ⟨x,hnf.2.1.symm ▸ mem_iUnion₂.mpr ⟨C,hc,hx⟩⟩
    obtain ⟨x,hx⟩ := holly_firstComponent_nonempty O hnf un
    have hxU := hx.1
    rw [hnf.2.1] at hxU
    obtain ⟨D,hd,hxd⟩ := mem_iUnion₂.mp hxU
    have he := (hnf.piece_eq_component O hd hxd).trans (firstComponent_eq_component hx).symm
    have dD : P.Definable₁ L D := he ▸ definable_firstComponent order hLE dU
    by_cases eqn : C = D
    · exact eqn ▸ dD
    let rest := cells.erase D
    have cov : U \ D = ⋃ T ∈ rest, T := by
      ext z
      constructor
      · rintro ⟨hz,out⟩
        rw [hnf.2.1] at hz
        obtain ⟨T,hT,ht⟩ := mem_iUnion₂.mp hz
        exact mem_iUnion₂.mpr ⟨T,Finset.mem_erase.mpr ⟨fun e => out (e ▸ ht),hT⟩,ht⟩
      · intro hz
        obtain ⟨T,hT,ht⟩ := mem_iUnion₂.mp hz
        obtain ⟨dif,mem⟩ := Finset.mem_erase.mp hT
        refine ⟨hnf.2.1.symm ▸ mem_iUnion₂.mpr ⟨T,mem,ht⟩,fun h => dif ?_⟩
        exact (hnf.piece_eq_component O mem ht).trans (hnf.piece_eq_component O hd h).symm
    have hrest : IsHollyDecomposition O (U \ D) rest :=
      ⟨fun T h => hnf.1 T (Finset.mem_of_mem_erase h),cov,fun B hB T hT =>
        hnf.2.2 B (Finset.mem_of_mem_erase hB) T (Finset.mem_of_mem_erase hT)⟩
    exact ih rest (Finset.card_erase_lt_of_mem hd) (U := U \ D) ((dU.sdiff dD) : P.Definable₁ L (U \ D)) hrest C (Finset.mem_erase.mpr ⟨eqn,hc⟩)

end GeneralizedEuler.Section3
